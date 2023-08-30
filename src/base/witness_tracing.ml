open Core_kernel

let render_writes = Option.is_none (Sys.getenv_opt "SKIP_WITNESS_RESULTS")

let render_empty = Option.is_some (Sys.getenv_opt "INCLUDE_EMPTY_CALLS")

module Cvar_access = struct
  (* TODO: add field values to Constant and Scale *)
  type t =
    | Witness of int
    | Public_input of int
    | Constant of string
    | Add of t * t
    | Scale of string * t
  [@@deriving compare]

  let rec sexp_of_t : t -> Sexp.t = function
    | Witness i ->
        Atom (sprintf "w[%d]" i)
    | Public_input i ->
        Atom (sprintf "pub[%d]" i)
    | Constant f ->
        Atom f
    | Add (a, b) ->
        List [ Atom "add"; sexp_of_t a; sexp_of_t b ]
    | Scale (f, c) ->
        List [ Atom "scale"; Atom f; sexp_of_t c ]

  let of_int s i =
    let num_inputs = Run_state.num_inputs s in
    if i < num_inputs then Public_input i else Witness (i - num_inputs)

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

  let sexp_of_result (i, _v) =
    (* TODO: include v if render_writes is true *)
    if render_writes then Sexp.Atom (sprintf "w[%d]" i)
    else Sexp.Atom (sprintf "w[%d]" i)

  type t =
    { mutable accesses : Cvar_access.t list [@sexp.omit_nil]
    ; mutable results : result list [@sexp.omit_nil]
    }

  let sexp_of_t = function
    | { accesses = []; results } ->
        Sexp.List ([ Sexp.Atom "push" ] @ List.map ~f:sexp_of_result results)
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
  type t =
    { label : string
    ; mutable exists_calls : Exists.t list [@sexp.omit_nil]
    ; mutable inner_calls : t list [@sexp.omit_nil]
    }
  [@@deriving sexp_of]

  let rec sexp_of_t = function
    | { label = v_label; exists_calls = [ exists_call ]; inner_calls = [] }
      when not (String.contains v_label ' ') ->
        (* Simple case that can be represented as a regular function call *)
        let accesses = List.map ~f:Cvar_access.sexp_of_t exists_call.accesses in
        let results = List.map ~f:Exists.sexp_of_result exists_call.results in
        Sexp.(List ([ Atom v_label ] @ accesses @ [ Atom "=>" ] @ results))
    | { label = v_label; exists_calls = [ exists_call ]; inner_calls = [] }
      when String.is_prefix v_label ~prefix:"if_:" ->
        (* Case for `if_` function *)
        let accesses =
          List.rev_map ~f:Cvar_access.sexp_of_t exists_call.accesses
        in
        let results = List.map ~f:Exists.sexp_of_result exists_call.results in
        Sexp.(List ([ Atom "if_" ] @ accesses @ [ Atom "=>" ] @ results))
    | { label = v_label
      ; exists_calls = v_exists_calls
      ; inner_calls = v_inner_calls
      } ->
        let bnds = [] in
        let bnds =
          match sexp_of_list sexp_of_t v_inner_calls with
          | Sexp.List [] ->
              bnds
          | arg ->
              Sexp.List [ Sexp.Atom "inner_calls"; arg ] :: bnds
        in
        let bnds =
          match sexp_of_list Exists.sexp_of_t v_exists_calls with
          | Sexp.List [] ->
              bnds
          | arg ->
              Sexp.List [ Sexp.Atom "exists_calls"; arg ] :: bnds
        in
        let bnds =
          let arg = sexp_of_string v_label in
          Sexp.List [ Sexp.Atom "label"; arg ] :: bnds
        in
        Sexp.List bnds

  let empty label = { label; exists_calls = []; inner_calls = [] }

  let no_empty_accesses t =
    render_empty
    || not (List.is_empty t.exists_calls && List.is_empty t.inner_calls)

  let call_stack = ref [ empty "(root)" ]

  let reset () = call_stack := [ empty "(root)" ]

  let push label =
    let call = empty label in
    let parent_call = List.hd_exn !call_stack in
    parent_call.inner_calls <- call :: parent_call.inner_calls ;
    call_stack := call :: !call_stack

  let pop () =
    let call = List.hd_exn !call_stack in
    call.inner_calls <-
      List.rev (List.filter ~f:no_empty_accesses call.inner_calls) ;
    call.exists_calls <-
      List.rev (List.filter ~f:Exists.no_empty_accesses call.exists_calls) ;
    call_stack := List.tl_exn !call_stack ;
    call

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
    if render_writes then exists.results <- (index, field) :: exists.results

  let begin_exists_call () =
    let call = List.hd_exn !call_stack in
    let exists = Exists.empty () in
    call.exists_calls <- exists :: call.exists_calls ;
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

let dump_current job_str filename =
  let call = Call.pop () in
  let call_sexp = Call.sexp_of_t call in
  let call_sexp_str = Sexp.to_string_hum call_sexp in
  let oc = Out_channel.create filename in
  Out_channel.output_string oc "Job:\n\n" ;
  Out_channel.output_string oc job_str ;
  Out_channel.output_string oc "\n\n=============\n\n" ;
  Out_channel.output_string oc call_sexp_str ;
  Out_channel.close oc

(*let log_stored_fields ~sexp_of_field s stored_fields =
  let stored_fields_sexp = List.sexp_of_t sexp_of_field stored_fields in
  let indent = 2 * List.length (Run_state.stack s) in
  let label = Option.value ~default:"(none)" @@ List.hd (Run_state.stack s) in
  let indent_str = String.make (Int.max 0 (indent - 2)) ' ' in
  let inputs_sexp =
    List.sexp_of_t Cvar_access.sexp_of_t Cvar_access.(get ())
  in
  eprintf "%s%s: {\n" indent_str label ;
  (* (*if List.length !stored_fields <= 1 then
           eprintf "%s%s: %s\n%!" indent_str label
             (Sexp.to_string_hum stored_fields_sexp)
         else*)
       eprintf "%s%s:\n%s input:\n%s  %s\n%s  %s\n%!" indent_str label
         indent_str indent_str inputs indent_str
         (Sexp.to_string_hum ~indent:(indent + 1) stored_fields_sexp)
     else*)
  eprintf "%s in: %s\n" indent_str
    (Sexp.to_string_hum ~indent:(indent + 1) inputs_sexp) ;
  if false then
    eprintf "%s out:\n%s  %s\n" indent_str indent_str
      (Sexp.to_string_hum ~indent:(indent + 1) stored_fields_sexp) ;
  eprintf "%s}\n%!" indent_str*)
