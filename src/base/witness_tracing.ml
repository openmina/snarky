open Core_kernel

let render_writes = Option.is_some (Sys.getenv_opt "INCLUDE_WITNESS_RESULTS")

let render_empty = Option.is_some (Sys.getenv_opt "INCLUDE_EMPTY_CALLS")

module Trace = struct
  type t =
    { name : string
    ; mutable priv_indexes : Int.Set.t
    ; mutable trace_sexp : Sexp.t
    }

  let empty ~name () =
    { name; priv_indexes = Int.Set.empty; trace_sexp = Sexp.Atom "empty" }
end

let current_trace = ref (Trace.empty ~name:"(root)" ())

let captured_traces = ref []

module Cvar_access = struct
  type t =
    | Witness of int
    | Public_input of int
    | Private_input of int
    | Constant of string
    | Add of t * t
    | Scale of string * t
  [@@deriving compare]

  let rec sexp_of_t : t -> Sexp.t = function
    | Witness i ->
        Atom (sprintf "w[%d]" i)
    | Public_input i ->
        Atom (sprintf "pub[%d]" i)
    | Private_input i ->
        Atom (sprintf "priv[%d]" i)
    | Constant f ->
        Atom f
    | Add (a, b) ->
        List [ Atom "add"; sexp_of_t a; sexp_of_t b ]
    | Scale (f, c) ->
        List [ Atom "scale"; Atom f; sexp_of_t c ]

  let of_int s i =
    let num_inputs = Run_state.num_inputs s in
    let wi = i - num_inputs in
    if i < num_inputs then Public_input i
    else if Int.Set.mem !current_trace.priv_indexes wi then Private_input wi
    else Witness wi

  let rec of_cvar_sexp s (cs : Sexp.t) =
    match cs with
    | List [ Atom "Constant"; Atom f ] ->
        Constant f
    | List [ Atom "Var"; Atom n ] ->
        of_int s (int_of_string n)
    | List [ Atom "Add"; a; b ] ->
        Add (of_cvar_sexp s a, of_cvar_sexp s b)
    | List [ Atom "Scale"; Atom f; cs ] ->
        Scale (f, of_cvar_sexp s cs)
    | other ->
        eprintf "+++ Unexpected Cvar sexp found during witness tracing: %s\n%!"
          (Sexp.to_string_hum other) ;
        assert false
end

module Exists = struct
  type result = int * string

  let is_not_consecutive (i, _) (j, _) = i + 1 <> j

  let sexp_of_result (i, v) =
    let kind = if Set.mem !current_trace.priv_indexes i then "priv" else "w" in
    if render_writes then Sexp.Atom (sprintf "%s[%d]=%s" kind i v)
    else Sexp.Atom (sprintf "%s[%d]" kind i)

  let sexp_of_result_list results =
    match results with
    | [] ->
        []
    | [ r1 ] ->
        [ sexp_of_result r1 ]
    | [ r1; r2 ] ->
        [ sexp_of_result r1; sexp_of_result r2 ]
    | results when render_writes ->
        List.map ~f:sexp_of_result results
    | results ->
        results
        |> List.group ~break:is_not_consecutive
        |> List.concat_map ~f:(function
             | [ one ] ->
                 [ sexp_of_result one ]
             | [ one; two ] ->
                 [ sexp_of_result one; sexp_of_result two ]
             | many ->
                 let first_i = fst @@ List.hd_exn many in
                 let last_i = fst @@ List.last_exn many in
                 let kind =
                   if Set.mem !current_trace.priv_indexes first_i then "priv"
                   else "w"
                 in
                 [ Sexp.Atom (sprintf "%s[%d..%d]" kind first_i last_i) ] )

  type t =
    { mutable accesses : Cvar_access.t list; mutable results : result list }

  let sexp_of_t = function
    | { accesses = []; results } ->
        Sexp.List ([ Sexp.Atom "push" ] @ sexp_of_result_list results)
    | { accesses; results = [] } ->
        Sexp.List
          ([ Sexp.Atom "read" ] @ List.map ~f:Cvar_access.sexp_of_t accesses)
    | { accesses; results } ->
        Sexp.List
          ( [ Sexp.Atom "exists" ]
          @ List.map ~f:Cvar_access.sexp_of_t accesses
          @ [ Sexp.Atom "=>" ]
          @ List.map ~f:sexp_of_result results )

  let empty () = { accesses = []; results = [] }

  let no_empty_accesses t = render_empty || not (List.is_empty t.results)
end

module Call = struct
  type label = { label : string; mutable inner_calls : t list }

  and t = Label of label | Exists of Exists.t

  let not_consecutive a b =
    match (a, b) with
    | ( Exists { accesses = []; results = [ (i, _) ] }
      , Exists { accesses = []; results = [ (j, _) ] } )
      when not render_writes ->
        not (i + 1 = j)
    | _ ->
        true

  let rec sexp_of_t = function
    | Label { label = v_label; inner_calls = [ Exists exists_call ] }
      when not (String.contains v_label ' ') ->
        (* Simple case that can be represented as a regular function call *)
        let accesses = List.map ~f:Cvar_access.sexp_of_t exists_call.accesses in
        let results = Exists.sexp_of_result_list exists_call.results in
        Sexp.(List ([ Atom v_label ] @ accesses @ [ Atom "=>" ] @ results))
    | Label { label = v_label; inner_calls = [ Exists exists_call ] }
      when String.is_prefix v_label ~prefix:"if_:" ->
        (* Case for `if_` function *)
        let accesses =
          List.rev_map ~f:Cvar_access.sexp_of_t exists_call.accesses
        in
        let results = Exists.sexp_of_result_list exists_call.results in
        Sexp.(List ([ Atom "if_" ] @ accesses @ [ Atom "=>" ] @ results))
    | Label { label = v_label; inner_calls = v_inner_calls } ->
        let bnds = [] in
        let bnds =
          match sexp_of_t_list v_inner_calls with
          | Sexp.List [] ->
              bnds
          | arg ->
              Sexp.List [ Sexp.Atom "inner_calls"; arg ] :: bnds
        in
        let bnds =
          let arg = sexp_of_string v_label in
          Sexp.List [ Sexp.Atom "label"; arg ] :: bnds
        in
        Sexp.List bnds
    | Exists exists ->
        Exists.sexp_of_t exists

  and sexp_of_t_list calls =
    Sexp.List
      ( calls
      |> List.group ~break:not_consecutive
      |> List.concat_map ~f:(function
           | [ one ] ->
               [ sexp_of_t one ]
           | [ one; two ] ->
               [ sexp_of_t one; sexp_of_t two ]
           | many ->
               let first = List.hd_exn many in
               let last = List.last_exn many in
               [ List
                   [ Atom "for"; sexp_of_t first; Atom "-->"; sexp_of_t last ]
               ] ) )

  let empty label = Label { label; inner_calls = [] }

  let no_empty_accesses = function
    | Label t ->
        render_empty || not (List.is_empty t.inner_calls)
    | Exists exists ->
        Exists.no_empty_accesses exists

  let call_stack = ref [ empty "(root)" ]

  let inside_request = ref [ false ]

  let reset ?(root_label = "(root)") () =
    call_stack := [ empty root_label ] ;
    inside_request := [ false ] ;
    current_trace := Trace.empty ~name:root_label ()

  let push label =
    let lbl = empty label in
    inside_request :=
      String.is_substring ~substring:"@request=" label :: !inside_request ;
    match List.hd_exn !call_stack with
    | Exists _ ->
        prerr_endline
          "Call.push: Got an unexpected `Exists` at top of call stack" ;
        assert false
    | Label parent_call ->
        parent_call.inner_calls <- lbl :: parent_call.inner_calls ;
        call_stack := lbl :: !call_stack

  let pop () =
    match List.hd_exn !call_stack with
    | Exists _ ->
        prerr_endline
          "Call.pop: Got an unexpected `Exists` at top of call stack" ;
        assert false
    | Label call as lbl ->
        call.inner_calls <-
          List.rev (List.filter ~f:no_empty_accesses call.inner_calls) ;
        call_stack := List.tl_exn !call_stack ;
        inside_request := List.tl_exn !inside_request ;
        lbl

  let exists_stack = ref []

  let track_read s cvar =
    let open Exists in
    if Run_state.has_witness s then
      try
        let exists = List.hd_exn !exists_stack in
        exists.accesses <- Cvar_access.of_cvar_sexp s cvar :: exists.accesses
      with _ -> ()
  (* TODO: log a warning if this happens *)

  let track_write ~index field =
    let exists = List.hd_exn !exists_stack in
    let inside_request = List.hd_exn !inside_request in
    if inside_request then
      !current_trace.priv_indexes <-
        Int.Set.add !current_trace.priv_indexes index ;
    exists.results <- (index, field) :: exists.results

  let begin_exists_call () =
    match List.hd_exn !call_stack with
    | Exists _ ->
        prerr_endline
          "begin_exists_call: Got an unexpected `Exists` at top of call stack" ;
        assert false
    | Label call ->
        let exists = Exists.empty () in
        call.inner_calls <- Exists exists :: call.inner_calls ;
        exists_stack := exists :: !exists_stack

  let end_exists_call () =
    let exists = List.hd_exn !exists_stack in
    exists_stack := List.tl_exn !exists_stack ;
    (* TODO: reverse reads? *)
    (*exists.accesses <-
      List.dedup_and_sort ~compare:Cvar_access.compare exists.accesses ;*)
    exists.results <- List.rev exists.results
end

module Label = struct
  let enter label = Call.push label

  let exit () = ignore (Call.pop ())

  let wrap label f =
    enter label ;
    let result = f () in
    exit () ; result
end

let setup () = Call.reset ()

let begin_exists_call = Call.begin_exists_call

let end_exists_call = Call.end_exists_call

let track_access = Call.track_read

let track_write = Call.track_write

let capture_begin root_label = Call.reset ~root_label ()

let capture_end () =
  !current_trace.trace_sexp <- Call.sexp_of_t (Call.pop ()) ;
  captured_traces := !current_trace :: !captured_traces

let dump_current job_str base_path =
  Core.Unix.mkdir_p base_path;
    let job_json_filename = Filename.concat base_path "spec.json" in
  Out_channel.write_all job_json_filename ~data:job_str ;
  List.iter !captured_traces ~f:(fun trace ->
      let filename = Filename.concat base_path (trace.name ^ ".sexp") in
      Out_channel.write_all filename ~data:(Sexp.to_string_hum trace.trace_sexp) )
