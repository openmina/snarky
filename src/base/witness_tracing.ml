open Core_kernel

let render_writes = Option.is_some (Sys.getenv_opt "INCLUDE_WITNESS_RESULTS")

let render_empty = Option.is_some (Sys.getenv_opt "INCLUDE_EMPTY_CALLS")

module Cvar_access = struct
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

  let is_not_consecutive (i, _) (j, _) = i + 1 <> j

  let sexp_of_result (i, v) =
    if render_writes then Sexp.Atom (sprintf "w[%d]=%s" i v)
    else Sexp.Atom (sprintf "w[%d]" i)

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
                 [ Sexp.Atom (sprintf "w[%d..%d]" first_i last_i) ] )

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
               [ sexp_of_t first; Atom "-->"; sexp_of_t last ] ) )

  let empty label = Label { label; inner_calls = [] }

  let no_empty_accesses = function
    | Label t ->
        render_empty || not (List.is_empty t.inner_calls)
    | Exists exists ->
        Exists.no_empty_accesses exists

  let call_stack = ref [ empty "(root)" ]

  let reset () = call_stack := [ empty "(root)" ]

  let push label =
    let lbl = empty label in
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
