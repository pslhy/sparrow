open SlicingUtils
open Global

module Line = struct
  type t = string * string

  let compare = Stdlib.compare

  let equal = ( = )

  let hash = Hashtbl.hash
end

module LineLevelG = Graph.Imperative.Digraph.ConcreteBidirectional (Line)

module W = struct
  type edge = LineLevelG.E.t

  type t = int

  let weight _ = 1

  let compare = compare

  let add = ( + )

  let zero = 0
end

module Dijkstra = Graph.Path.Dijkstra (LineLevelG) (W)

module Bfs = Graph.Traverse.Bfs (LineLevelG)

type t = { graph : LineLevelG.t; target : Line.t }

let add_edge global graph src_node dst_node =
  let src_func = SlicingUtils.node_to_funcname global src_node in
  let src_line = SlicingUtils.node_to_lstr global src_node in
  let src = (src_func, src_line) in
  let dst_func = SlicingUtils.node_to_funcname global dst_node in
  let dst_line = SlicingUtils.node_to_lstr global dst_node in
  let dst = (dst_func, dst_line) in
  if not (LineLevelG.V.equal src dst) then LineLevelG.add_edge graph src dst

let init global targ_func targ_line edge_set =
  let graph = LineLevelG.create () in
  let target = (targ_func, targ_line) in
  EdgeSet.iter (fun (src, dst) -> add_edge global graph src dst) edge_set;
  { graph; target }

let get_pathcounts dfg sink =
  let get_entries graph target resset =
    LineLevelG.fold_vertex (fun v acc -> if LineLevelG.pred graph v = [] then BatSet.add v acc else acc) graph BatSet.empty
  in
  let rec succ_pathcounter graph worklist resmap =
    match worklist with
    | [] -> resmap 
    | target :: tl -> 
      if BatMap.mem target resmap then succ_pathcounter graph tl resmap
      else
        let succs = LineLevelG.succ graph target in
        if succs = [] then
          succ_pathcounter graph tl (BatMap.add target 1 resmap)
        else
          let calculatable = BatList.fold (fun acc succ -> acc && BatMap.mem succ resmap) true (LineLevelG.succ graph target)  in
          if calculatable then
            let sc = BatList.fold (fun acc succ -> acc + BatMap.find succ resmap) 0 (LineLevelG.succ graph target)  in
            succ_pathcounter graph tl (BatMap.add target sc resmap)
          else
            succ_pathcounter graph ((LineLevelG.succ graph target) :: tl) resmap
  in
  let rec pred_pathcounter graph target resmap =
    if BatMap.mem target resmap then resmap
    else
      let newmap = BatList.fold (fun acc pred -> pred_pathcounter graph pred acc) resmap (LineLevelG.pred graph target) in
      let pc = BatList.fold (fun acc pred  -> acc + BatMap.find pred newmap) 0 (LineLevelG.pred graph target)  in
      let pred_count = if pc = 0 then 1 else pc in
      BatMap.add target pred_count newmap
  in
  let entries = get_entries dfg sink BatSet.empty in
  let succ_pathcount = succ_pathcounter dfg [entries] BatMap.empty in
  let pred_pathcount = pred_pathcounter dfg sink BatMap.empty in
  BatMap.merge (fun _ a b -> match a, b with
      | Some x, Some y -> Some (x, y)
      | _ -> None) pred_pathcount succ_pathcount

let rec list_max = function
  | [] -> failwith "empty list to list_max()"
  | [ x ] -> x
  | head :: tail ->
      let tail_max = list_max tail in
      if head > tail_max then head else tail_max

let stringfy_nodes global dfg =
  let pids = InterCfg.pidsof global.icfg in
  let pcm = get_pathcounts dfg.graph dfg.target in
  let folder v acc_entries =
    let func, line = v in
    let pred_count, succ_count = try BatMap.find v pcm with Not_found -> (0,0) in
    let dist = Dijkstra.shortest_path dfg.graph v dfg.target |> snd in
    if not (List.mem func pids) then acc_entries
    else (dist, (pred_count*succ_count, line)) :: acc_entries
  in
  let entries = LineLevelG.fold_vertex folder dfg.graph [] in
  let max_dist = List.map fst entries |> list_max in
  let folder acc_strs (dist, (pathcount, line)) =
    SS.add (Printf.sprintf "%d %d %s" (max_dist - dist + 1) pathcount line) acc_strs
  in
  List.fold_left folder SS.empty entries