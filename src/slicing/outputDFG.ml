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
  let rec explore graph worklist resmap =
    if Queue.is_empty worklist then resmap
    else
      let task = (Queue.pop worklist) in
      let node = List.hd task in
      if List.length (LineLevelG.pred graph node) = 0 then
        let resmap' = List.fold_left (fun m v -> BatMap.add v (try BatMap.find v m with Not_found -> 0) + 1 m) resmap task in
        explore graph worklist resmap'
      else
        let worklist' = LineLevelG.fold_pred (fun pred wl -> Queue.push ([pred] @ task) wl) graph node worklist in
        explore graph worklist' resmap
  in
  let worklist = Queue.add [sink] (Queue.create ()) in
  explore dfg worklist BatMap.empty

let rec list_max = function
  | [] -> failwith "empty list to list_max()"
  | [ x ] -> x
  | head :: tail ->
      let tail_max = list_max tail in
      if head > tail_max then head else tail_max

let stringfy_nodes global dfg =
  let pids = InterCfg.pidsof global.icfg in
  let pcs = get_pathcounts dfg dfg.target in
  let folder v acc_entries =
    let func, line = v in
    let pathcount = try BatMap.find v pcs with Not_found -> 0 in
    let dist = Dijkstra.shortest_path dfg.graph v dfg.target |> snd in
    if not (List.mem func pids) then acc_entries
    else ((dist, pathcount), line) :: acc_entries
  in
  let entries = LineLevelG.fold_vertex folder dfg.graph [] in
  let max_dist = List.map fst entries |> list_max in
  let folder acc_strs ((dist, pathcount), line) =
    SS.add (Printf.sprintf "%d %d %s" (max_dist - dist + 1) pathcount line) acc_strs
  in
  List.fold_left folder SS.empty entries