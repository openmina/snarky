open Core_kernel
module Types0 = Types

module Make
    (Backend : Backend_extended.S)
    (Checked : Checked_intf.Extended with type field = Backend.Field.t)
    (As_prover : As_prover0.Extended with type field := Backend.Field.t)
    (Runner : Checked_runner.S
                with module Types := Checked.Types
                with type field := Backend.Field.t
                 and type cvar := Backend.Cvar.t
                 and type constr := Backend.Constraint.t option
                 and type r1cs := Backend.R1CS_constraint_system.t) =
struct
  open Backend

  let set_constraint_logger = Runner.set_constraint_logger

  let clear_constraint_logger = Runner.clear_constraint_logger

  type field = Field.t

  let field_vec_id : Field.Vector.t Type_equal.Id.t =
    Type_equal.Id.create ~name:"field-vector" sexp_of_opaque

  let pack_field_vec v =
    Run_state.Vector.T ((module Field.Vector), field_vec_id, v)

  let field_vec () = pack_field_vec (Field.Vector.create ())

  module Proof_inputs = struct
    type t =
      { public_inputs : Field.Vector.t; auxiliary_inputs : Field.Vector.t }
  end

  module Bigint = Bigint
  module Field0 = Field
  module Cvar = Cvar
  module Constraint = Constraint

  module Handler = struct
    type t = Request.request -> Request.response
  end

  module Runner = Runner

  (* TODO-someday: Add pass to unify variables which have an Equal constraint *)
  let constraint_system ~run ~num_inputs ~return_typ:(Types.Typ.Typ return_typ)
      output t : R1CS_constraint_system.t =
    let input = field_vec () in
    let next_auxiliary = ref (1 + num_inputs) in
    let aux = field_vec () in
    let system = R1CS_constraint_system.create () in
    let state =
      Runner.State.make ~num_inputs ~input ~next_auxiliary ~aux ~system
        ~with_witness:false ()
    in
    let state, res = run t state in
    let res, _ = return_typ.var_to_fields res in
    let output, _ = return_typ.var_to_fields output in
    let _state =
      Array.fold2_exn ~init:state res output ~f:(fun state res output ->
          fst @@ Checked.run (Checked.assert_equal res output) state )
    in
    let auxiliary_input_size = !next_auxiliary - (1 + num_inputs) in
    R1CS_constraint_system.set_auxiliary_input_size system auxiliary_input_size ;
    system

  let auxiliary_input ?system ~run ~num_inputs
      ?(handlers = ([] : Handler.t list)) t0 (input : Field.Vector.t)
      ~return_typ:(Types.Typ.Typ return_typ) ~output : Field.Vector.t * _ =
    let next_auxiliary = ref (1 + num_inputs) in
    let aux = Field.Vector.create () in
    let handler =
      List.fold ~init:Request.Handler.fail handlers ~f:(fun handler h ->
          Request.Handler.(push handler (create_single h)) )
    in
    let state =
      Runner.State.make ?system ~num_inputs ~input:(pack_field_vec input)
        ~next_auxiliary ~aux:(pack_field_vec aux) ~handler ~with_witness:true ()
    in
    let state, res = run t0 state in
    let res, auxiliary_output_data = return_typ.var_to_fields res in
    let output, _ = return_typ.var_to_fields output in
    let _state =
      Array.fold2_exn ~init:state res output ~f:(fun state res output ->
          Field.Vector.emplace_back input (Runner.get_value state res) ;
          fst @@ Checked.run (Checked.assert_equal res output) state )
    in
    let true_output =
      return_typ.var_of_fields (output, auxiliary_output_data)
    in
    Option.iter system ~f:(fun system ->
        let auxiliary_input_size = !next_auxiliary - (1 + num_inputs) in
        R1CS_constraint_system.set_auxiliary_input_size system
          auxiliary_input_size ;
        R1CS_constraint_system.finalize system ) ;
    (aux, true_output)

  let run_and_check' ~run t0 =
    let num_inputs = 0 in
    let input = field_vec () in
    let next_auxiliary = ref 1 in
    let aux = Field.Vector.create () in
    let system = R1CS_constraint_system.create () in
    let get_value : Cvar.t -> Field.t =
      let get_one v = Field.Vector.get aux (v - 1) in
      Cvar.eval (`Return_values_will_be_mutated get_one)
    in
    let state =
      Runner.State.make ~num_inputs ~input ~next_auxiliary
        ~aux:(pack_field_vec aux) ~system ~eval_constraints:true
        ~with_witness:true ()
    in
    match run t0 state with
    | exception e ->
        Or_error.of_exn ~backtrace:`Get e
    | _, x ->
        Ok (x, get_value)

  let run_and_check_deferred' ~map ~return ~run t0 =
    let num_inputs = 0 in
    let input = field_vec () in
    let next_auxiliary = ref 1 in
    let aux = Field.Vector.create () in
    let system = R1CS_constraint_system.create () in
    let get_value : Cvar.t -> Field.t =
      let get_one v = Field.Vector.get aux (v - 1) in
      Cvar.eval (`Return_values_will_be_mutated get_one)
    in
    let state =
      Runner.State.make ~num_inputs ~input ~next_auxiliary
        ~aux:(pack_field_vec aux) ~system ~eval_constraints:true
        ~with_witness:true ()
    in
    match run t0 state with
    | exception e ->
        return (Or_error.of_exn ~backtrace:`Get e)
    | res ->
        map res ~f:(function _, x -> Ok (x, get_value))

  let run_unchecked ~run t0 =
    let num_inputs = 0 in
    let input = field_vec () in
    let next_auxiliary = ref 1 in
    let aux = field_vec () in
    let state =
      Runner.State.make ~num_inputs ~input ~next_auxiliary ~aux
        ~with_witness:true ()
    in
    match run t0 state with _, x -> x

  let run_and_check ~run t =
    Or_error.map (run_and_check' ~run t) ~f:(fun (x, get_value) ->
        let x = As_prover.run x get_value in
        x )

  let check ~run t = run_and_check' ~run t |> Result.map ~f:(Fn.const ())

  module Run = struct
    let alloc_var next_input () =
      let v = !next_input in
      incr next_input ; Cvar.Unsafe.of_index v

    let store_field_elt primary_input next_input x =
      let v = alloc_var next_input () in
      Field.Vector.emplace_back primary_input x ;
      v

    let collect_input_constraints :
        type checked input_var input_value.
           int ref
        -> input_typ:
             ( input_var
             , input_value
             , field
             , (unit, field) Checked.Types.Checked.t )
             Types.Typ.typ
        -> return_typ:_ Types.Typ.t
        -> (unit -> input_var -> checked)
        -> _ * (unit -> checked) Checked.t =
     fun next_input ~input_typ:(Typ input_typ) ~return_typ:(Typ return_typ) k ->
      let open Checked in
      let alloc_input
          { Types0.Typ.var_of_fields
          ; size_in_field_elements
          ; constraint_system_auxiliary
          ; _
          } =
        var_of_fields
          ( Core_kernel.Array.init size_in_field_elements ~f:(fun _ ->
                alloc_var next_input () )
          , constraint_system_auxiliary () )
      in
      let var = alloc_input input_typ in
      let retval = alloc_input return_typ in
      let checked =
        let%bind () = input_typ.check var in
        Checked.return (fun () -> k () var)
      in
      (retval, checked)

    let r1cs_h :
        type a checked input_var input_value retval.
           run:(a, checked) Runner.run
        -> int ref
        -> input_typ:
             ( input_var
             , input_value
             , field
             , (unit, field) Checked.Types.Checked.t )
             Types.Typ.typ
        -> return_typ:(a, retval, _, _) Types.Typ.t
        -> (input_var -> checked)
        -> R1CS_constraint_system.t =
     fun ~run next_input ~input_typ ~return_typ k ->
      let retval, r =
        collect_input_constraints next_input ~input_typ ~return_typ (fun () ->
            k )
      in
      let run_in_run r state =
        let state, x = Checked.run r state in
        run x state
      in
      constraint_system ~run:run_in_run ~num_inputs:(!next_input - 1)
        ~return_typ retval
        (Checked.map ~f:(fun r -> r ()) r)

    let constraint_system (type a checked input_var) :
           run:(a, checked) Runner.run
        -> input_typ:(input_var, _, _, _) Types.Typ.typ
        -> return_typ:_
        -> (input_var -> checked)
        -> R1CS_constraint_system.t =
     fun ~run ~input_typ ~return_typ k ->
      r1cs_h ~run (ref 1) ~input_typ ~return_typ k

    let generate_public_input :
           ('input_var, 'input_value, _, _) Types.Typ.typ
        -> 'input_value
        -> Field.Vector.t =
     fun (Typ { value_to_fields; _ }) value ->
      let primary_input = Field.Vector.create () in
      let next_input = ref 1 in
      let store_field_elt = store_field_elt primary_input next_input in
      let fields, _aux = value_to_fields value in
      let _fields = Array.map ~f:store_field_elt fields in
      primary_input

    let conv :
        type r_var r_value.
           (int -> _ -> r_var -> Field.Vector.t -> r_value)
        -> ('input_var, 'input_value, _, _) Types.Typ.t
        -> _ Types.Typ.t
        -> (unit -> 'input_var -> r_var)
        -> 'input_value
        -> r_value =
     fun cont0 input_typ (Typ return_typ) k0 ->
      let primary_input = Field.Vector.create () in
      let next_input = ref 1 in
      let store_field_elt x =
        let v = !next_input in
        incr next_input ;
        Field.Vector.emplace_back primary_input x ;
        Cvar.Unsafe.of_index v
      in
      let (Typ { var_of_fields; value_to_fields; _ }) = input_typ in
      fun value ->
        let fields, aux = value_to_fields value in
        let fields = Array.map ~f:store_field_elt fields in
        let var = var_of_fields (fields, aux) in
        let retval =
          return_typ.var_of_fields
            ( Core_kernel.Array.init return_typ.size_in_field_elements
                ~f:(fun _ -> alloc_var next_input ())
            , return_typ.constraint_system_auxiliary () )
        in
        cont0 !next_input retval (k0 () var) primary_input

    let generate_auxiliary_input :
           run:('a, 'checked) Runner.run
        -> input_typ:_ Types.Typ.t
        -> return_typ:(_, _, _, _) Types.Typ.t
        -> ?handlers:Handler.t list
        -> 'k_var
        -> 'k_value =
     fun ~run ~input_typ ~return_typ ?handlers k ->
      conv
        (fun num_inputs output c primary ->
          let auxiliary =
            auxiliary_input ~run ?handlers ~return_typ ~output ~num_inputs c
              primary
          in
          ignore auxiliary )
        input_typ return_typ
        (fun () -> k)

    let generate_witness_conv :
           run:('a, 'checked) Runner.run
        -> f:(Proof_inputs.t -> _ -> 'out)
        -> input_typ:_ Types.Typ.t
        -> return_typ:_ Types.Typ.t
        -> ?handlers:Handler.t list
        -> 'k_var
        -> 'k_value =
     fun ~run ~f ~input_typ ~return_typ ?handlers k ->
      conv
        (fun num_inputs output c primary ->
          let auxiliary, output =
            auxiliary_input ~run ?handlers ~return_typ ~output ~num_inputs c
              primary
          in
          let output =
            let (Typ return_typ) = return_typ in
            let fields, aux = return_typ.var_to_fields output in
            let read_cvar =
              let get_one i =
                if i <= num_inputs then Field.Vector.get primary (i - 1)
                else Field.Vector.get auxiliary (i - num_inputs - 1)
              in
              Cvar.eval (`Return_values_will_be_mutated get_one)
            in
            let fields = Array.map ~f:read_cvar fields in
            return_typ.value_of_fields (fields, aux)
          in
          f
            { Proof_inputs.public_inputs = primary
            ; auxiliary_inputs = auxiliary
            }
            output )
        input_typ return_typ
        (fun () -> k)

    let generate_witness =
      generate_witness_conv ~f:(fun inputs _output -> inputs)
  end

  module Perform = struct
    let generate_witness ~run t ~return_typ k =
      Run.generate_witness ~run t ~return_typ k

    let generate_witness_conv ~run ~f t ~return_typ k =
      Run.generate_witness_conv ~run ~f t ~return_typ k

    let constraint_system = Run.constraint_system

    let run_unchecked = run_unchecked

    let run_and_check = run_and_check

    let check = check
  end

  let conv f spec return_typ k =
    Run.conv (fun _ _ x _ -> f x) spec return_typ (fun () -> k)

  let generate_auxiliary_input ~input_typ ~return_typ k =
    Run.generate_auxiliary_input ~run:Checked.run ~input_typ ~return_typ k

  let generate_public_input = Run.generate_public_input

  let generate_witness ~input_typ ~return_typ k =
    Run.generate_witness ~run:Checked.run ~input_typ ~return_typ k

  let generate_witness_conv ~f ~input_typ ~return_typ k =
    Run.generate_witness_conv ~run:Checked.run ~f ~input_typ ~return_typ k

  let constraint_system ~input_typ ~return_typ k =
    Run.constraint_system ~run:Checked.run ~input_typ ~return_typ k

  let run_unchecked t = run_unchecked ~run:Checked.run t

  let run_and_check t = run_and_check ~run:Checked.run t

  let check t = check ~run:Checked.run t
end
