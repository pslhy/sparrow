(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)
open Graph
open Cil
open Global
open Vocab

module L = Logging

(* transformation based on syntactic heuristics *)
let transform_simple file =
  opt !Options.unsound_alloc UnsoundAlloc.transform file

(* transformation based on semantic heuristics *)
let transform : Global.t -> Global.t
= fun global ->
  let loop_transformed = UnsoundLoop.transform global in
  let inlined = Frontend.inline global in
  if not !Options.il && (loop_transformed || inlined) then   (* something transformed *)
    Frontend.makeCFGinfo global.file    (* NOTE: CFG must be re-computed after transformation *)
    |> StepManager.stepf true "Translation to graphs (after inline)" Global.init
    |> StepManager.stepf true "Pre-analysis (after inline)" PreAnalysis.perform
  else global (* nothing changed *)

let marshal_in file =
  let filename = Filename.basename file.Cil.fileName in
  MarshalManager.input (filename ^ ".global")

let marshal_out file global =
  let filename = Filename.basename file.Cil.fileName in
  MarshalManager.output (filename ^ ".global") global;
  global

let init_analysis file =
  if !Options.marshal_in then marshal_in file
  else
    file
    |> transform_simple
    |> StepManager.stepf true "Translation to graphs" Global.init
    |> StepManager.stepf true "Pre-analysis" PreAnalysis.perform
    |> transform
    |> opt !Options.marshal_out (marshal_out file)

let print_pgm_info global =
  let pids = InterCfg.pidsof global.icfg in
  let nodes = InterCfg.nodesof global.icfg in
  L.info "#Procs : %d\n" (List.length pids);
  L.info "#Nodes : %d\n" (List.length nodes);
  global

let print_il file =
  (if !Options.inline = [] && BatSet.is_empty !Options.unsound_loop then
    Cil.dumpFile !Cil.printerForMaincil stdout "" (transform_simple file)
  else
    let global = init_analysis file in
    Cil.dumpFile !Cil.printerForMaincil stdout "" global.file);
  exit 0

let print_cfg : Global.t -> Global.t
= fun global ->
  `Assoc
    [ ("callgraph", CallGraph.to_json global.callgraph);
      ("cfgs", InterCfg.to_json global.icfg)]
  |> Yojson.Safe.pretty_to_channel stdout; exit 0

let finalize t0 =
  L.info ~level:1 "Finished properly.\n";
  Profiler.report stdout;
  L.info ~level:1 "%f\n" (Sys.time () -. t0);
  L.finalize ()

let octagon_analysis (global,itvinputof,_,_) =
  StepManager.stepf true "Oct Sparse Analysis" OctAnalysis.do_analysis (global,itvinputof)
  |> (fun (global,_,_,alarm) -> (global, alarm))

let taint_analysis (global,itvinputof,_,_) =
  StepManager.stepf true "Taint Sparse Analysis" TaintAnalysis.do_analysis (global,itvinputof)
  |> (fun (global,_,_,alarm) -> (global, alarm))

let extract_feature : Global.t -> Global.t
= fun global ->
  if !Options.extract_loop_feat then
    let _ = UnsoundLoop.extract_feature global |> UnsoundLoop.print_feature in
    exit 0
  else if !Options.extract_lib_feat then
    let _ = UnsoundLib.extract_feature global |> UnsoundLib.print_feature in
    exit 0
  else global

let mk_outdir dirname =
  if Sys.file_exists dirname && Sys.is_directory dirname then ()
  else if Sys.file_exists dirname && not (Sys.is_directory dirname) then
    let _ = L.error "Error: %s already exists." dirname in
    exit 1
  else
    Unix.mkdir dirname 0o755

let initialize () =
  Printexc.record_backtrace true;
  (* process arguments *)
  let usageMsg = "Usage: sparrow [options] source-files" in
  Arg.parse Options.opts Frontend.args usageMsg;
  mk_outdir !Options.outdir;
  L.init (if !Options.debug then L.DEBUG else L.INFO);
  L.info "%s\n" (String.concat " " !Frontend.files);
  Profiler.start_logger ();
  Cil.initCIL ()

let main () =
  let t0 = Sys.time () in
  initialize ();
  try
    StepManager.stepf true "Front-end" Frontend.parse ()
    |> Frontend.makeCFGinfo
    |> opt !Options.il print_il
    |> init_analysis
    |> print_pgm_info
    |> opt !Options.cfg print_cfg
    |> extract_feature
    |> StepManager.stepf true "Itv Sparse Analysis" ItvAnalysis.do_analysis
    |> case [ (!Options.oct, octagon_analysis);
              (!Options.taint, taint_analysis) ] (fun (global,_,_,alarm) -> (global, alarm))
    |> (fun (global, alarm) -> Report.print global alarm)
    |> (fun () -> finalize t0)
  with exc ->
    L.error "\n%s\n" (Printexc.to_string exc);
    L.error "%s\n" (Printexc.get_backtrace ());
    exit 1

let _ = main ()
