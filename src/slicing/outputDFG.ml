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

module Uint128 = Stdint.Uint128

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
  let rec get_entries graph worklist resset visited =
    match worklist with
    | [] -> resset
    | target :: tl ->
      let _ = Printf.printf "Get Entries :: Current %s, %d left \n" (snd target) (BatList.length tl) in 
      if BatSet.mem target visited then get_entries graph tl resset visited
      else
        let preds = LineLevelG.pred graph target in
        if  BatList.is_empty preds then
          let _ = Printf.printf "Get Entries :: Found Entry %s \n" (snd target) in
          get_entries graph tl (BatSet.add target resset) (BatSet.add target visited)
        else
          get_entries graph (preds @ tl) resset (BatSet.add target visited)
  in
  let rec pathcounter graph worklist incalculation resmap direction prefix =
    match worklist with
    | [] -> resmap 
    | target :: tl -> 
      if BatMap.mem target resmap then pathcounter graph tl (BatSet.remove target incalculation) resmap direction prefix
      else
        let _ = Printf.printf "%s Pathcounter :: Current %s, %d left \n" prefix (snd target) (BatList.length tl) in 
        let succs = direction graph target in
        let cal_succs = BatSet.elements (BatSet.diff (BatSet.of_list succs) incalculation) in
        if BatList.is_empty succs then
          pathcounter graph tl (BatSet.remove target incalculation) (BatMap.add target Uint128.one resmap) direction prefix
        else
          let calculatable = BatList.fold (fun acc succ -> acc && BatMap.mem succ resmap) true cal_succs  in
          if calculatable then
            let scc = BatList.fold (fun acc succ -> Uint128.add acc (BatMap.find succ resmap)) Uint128.zero cal_succs  in
            let sc = if scc = 0 then Uint128.one else scc in
            let _ = Printf.printf "%s Pathcounter :: Calculatable %s, Value %s, %s %d, %s \n" 
              prefix (snd target) (Uint128.to_string sc) prefix (BatList.length cal_succs) 
              (BatList.fold (fun acc succ -> acc ^ "+" ^ (Uint128.to_string (BatMap.find succ resmap))) "" cal_succs) 
            in 
            pathcounter graph tl (BatSet.remove target incalculation) (BatMap.add target sc resmap) direction prefix
          else
            pathcounter graph (cal_succs @ [target] @ tl) (BatSet.add target incalculation) resmap direction prefix
  in
  let entries = BatSet.to_list (get_entries dfg [sink] BatSet.empty BatSet.empty) in
  let succ_pathcount = pathcounter dfg entries BatSet.empty BatMap.empty LineLevelG.succ "Succ" in
  let pred_pathcount = pathcounter dfg [sink] BatSet.empty BatMap.empty LineLevelG.pred "Pred" in
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
    let pred_count, succ_count = try BatMap.find v pcm with Not_found -> (0L,0L) in
    let dist = Dijkstra.shortest_path dfg.graph v dfg.target |> snd in
    if not (List.mem func pids) then acc_entries
    else (dist, ((Uint128.mul pred_count succ_count), line)) :: acc_entries
  in
  let entries = LineLevelG.fold_vertex folder dfg.graph [] in
  let max_dist = List.map fst entries |> list_max in
  let folder acc_strs (dist, (pathcount, line)) =
    SS.add (Printf.sprintf "%d %s %s" (max_dist - dist + 1) (Uint128.to_string pathcount) line) acc_strs
  in
  List.fold_left folder SS.empty entries