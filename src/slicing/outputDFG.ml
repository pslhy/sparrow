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
  let rec explore graph snk resmap =
    (* (pred, succ) *)
    if BatMap.find snk resmap then resmap 
    else
      let pc = BatList.fold_left (fun acc pred -> 
          acc + (fst (BatMap.find pred (explore graph pred resmap)))
        ) 0 (LineLevelG.pred graph snk) in
      let pred_count = if pc = 0 then 1 else pc  in
      let sc = BatList.fold_left (fun acc succ -> 
        acc + (snd (BatMap.find succ (explore graph succ resmap)))
      ) 0 (LineLevelG.succ graph snk) in
      let succ_count = if sc = 0 then 1 else sc in
      BatMap.add snk (pred_count, succ_count) resmap
  in
  explore dfg.graph sink BatMap.empty


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