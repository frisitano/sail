open Libsail

open Type_check
open Ast
open Ast_compare
open Ast_defs
open Ast_util
open Bit
open Reporting
open Rewriter
open PPrint
open Pretty_print_common

module IntSet = Set.Make (Int)

(* Command line options *)
let opt_extern_types : string list ref = ref []

let opt_line_width : int ref = ref 100

let opt_semantic_range_types : bool ref = ref false

let opt_prop_dependent_types : (string * string) list ref = ref []

let opt_infer_prop_dependent_types : bool ref = ref false

(* Whether Sail's constraints are carried into Lean as proof obligations: a
   proof field on every constrained struct and a hypothesis on every function
   signature, both discharged by tactic.  This states in Lean what the Sail
   types actually say, but it only elaborates where the surrounding Lean types
   still carry the facts the obligation needs -- which erased `range` types,
   union payloads and dependent result bounds currently do not.  Off by
   default so the ordinary extraction stays buildable; see the Lean backend
   notes for what has to be restored first. *)
let opt_constraint_obligations : bool ref = ref false

let inferred_prop_dependent_records : string list ref = ref []

let prop_dependent_mode_active () =
  !opt_semantic_range_types || !opt_infer_prop_dependent_types || !opt_prop_dependent_types <> []
  || !inferred_prop_dependent_records <> []

type semantic_range = { low : nexp; high : nexp }

type prop_dependent_result = {
  result_name : string;
  result_quant : typquant;
  result_kopts : kinded_id list;
  result_params : kinded_id list;
  result_constraint : n_constraint;
  result_carrier : typ;
  result_typ : typ;
}

type semantic_types = {
  ranges : semantic_range Bindings.t;
  aliases : typ Bindings.t;
  alias_quants : typquant Bindings.t;
  valspecs : typ Bindings.t;
  valspec_quants : typquant Bindings.t;
  bindings : typ Bindings.t;
  record_fields : typ Bindings.t Bindings.t;
  record_quants : typquant Bindings.t;
}

let empty_semantic_types =
  {
    ranges = Bindings.empty;
    aliases = Bindings.empty;
    alias_quants = Bindings.empty;
    valspecs = Bindings.empty;
    valspec_quants = Bindings.empty;
    bindings = Bindings.empty;
    record_fields = Bindings.empty;
    record_quants = Bindings.empty;
  }

type global_context = {
  effect_info : Effects.side_effect_info;
  fun_args : string list Bindings.t;
  semantic_types : semantic_types;
  prop_dependent_results : prop_dependent_result Bindings.t;
  kid_id_renames : id option KBindings.t;
      (** Associates a kind variable to the corresponding argument of the function, used for implicit arguments. *)
  kid_id_renames_rev : kid Bindings.t;  (** Inverse of the [kid_id_renames] mapping. *)
}

let the_main_function_has_been_seen = ref false

let opt_noncomputable_functions : IdSet.t ref = ref IdSet.empty

let opt_partial_functions : IdSet.t ref = ref IdSet.empty

let non_beq_types : IdSet.t ref = ref IdSet.empty

let remove_empties (docs : document list) = List.filter (fun d -> d != empty) docs

let opens = ref IdSet.empty

let dependent_pair_instances_required = ref false

(* Quantified witnesses relevant to the unrefined carrier constructed by each
   function.  Only constraints connected to these witnesses become explicit
   proof arguments. *)
let prop_dependent_constraint_kids : KidSet.t Bindings.t ref = ref Bindings.empty

type context = {
  global : global_context;
  env : Type_check.env;
      (** The typechecking environment of the current function. This environment is reset using [initial_context] when
          we start processing a new function. Note that we use it to store paths of the form id.x.y.z. *)
  kid_id_renames : id option KBindings.t;
      (** Associates a kind variable to the corresponding argument of the function, used for implicit arguments. *)
  kid_id_renames_rev : kid Bindings.t;  (** Inverse of the [kid_id_renames] mapping. *)
  mutable loop_level : int;
  mutable if_level : int;
  in_sail_monad : bool;  (** Indicates whether we are in an expression of `SailM _` *)
  in_except_monad : document option;
      (** Indicates whether we are in an expression of `ExceptM _ _` what the return type is. *)
  semantic_return : typ option;
      (** The public semantic return type of the current function, when its internal carrier is different. *)
  dependent_return : typ option;
      (** The public existential return type of the current function, when its body uses the unpacked indexed value. *)
  dependent_result : prop_dependent_result option;
      (** A function-specific Prop-backed rendering of an eligible existential result. Unlike a generic Sail
          existential, this has an erased validity predicate rather than runtime Sigma witnesses. *)
  expected_dependent : typ option;
      (** The proof-refined result type expected for the current expression. This is consumed by the expression itself
          and is not propagated to its children. *)
  lean_bound_nvars : KidSet.t;
      (** Numeric kind variables that occur in the generated Lean signature and are therefore available as explicit or
          auto-implicit binders. *)
  function_bound_nvars : KidSet.t;
      (** Numeric kind variables bound by the function signature itself. Unlike [lean_bound_nvars], this excludes
          witnesses introduced while rendering local dependent expressions. *)
  unpacked_dependent_ids : IdSet.t;
      (** Local binders whose Sail type is existential, but whose generated Lean representation is the existential
          payload after a Sigma pattern or function-entry unpack. *)
  packed_dependent_types : typ Bindings.t;
      (** Local binders whose refined AST type is an existential payload, but whose generated Lean representation
          remains the public Sigma type because it is stored in a typed local or loop-carried aggregate. *)
  packed_dependent_results : prop_dependent_result Bindings.t;
      (** Local binders that retain a function-specific Prop-backed result wrapper rather than only its carrier. *)
  kid_docs : document KBindings.t;
      (** Local renderings for numeric kind variables recovered from fields of a proof-refined runtime carrier. *)
  dependent_pattern_kid_docs : document KBindings.t Bindings.t;
      (** Existential witness renderings associated with each value binder in a destructuring pattern. The same Sail
          kind names can be reused by successive existential results, so field projections must recover the witnesses
          belonging to their record rather than whichever witness was bound most recently. *)
  local_let_ids : IdSet.t;
      (** Value binders introduced by local lets, used to distinguish an unpacked existential carrier with anonymous
          witnesses from an indexed function argument whose type variables are in scope. *)
}

let context_init env global =
  {
    global;
    env;
    kid_id_renames = global.kid_id_renames;
    kid_id_renames_rev = global.kid_id_renames_rev;
    loop_level = 0;
    if_level = 0;
    in_sail_monad = false;
    in_except_monad = None;
    semantic_return = None;
    dependent_return = None;
    dependent_result = None;
    expected_dependent = None;
    lean_bound_nvars = KidSet.empty;
    function_bound_nvars = KidSet.empty;
    unpacked_dependent_ids = IdSet.empty;
    packed_dependent_types = Bindings.empty;
    packed_dependent_results = Bindings.empty;
    kid_docs = KBindings.empty;
    dependent_pattern_kid_docs = Bindings.empty;
    local_let_ids = IdSet.empty;
  }
let context_with_env ctx env = { ctx with env }

let add_single_kid_id_rename ctx id kid =
  let kir =
    match Bindings.find_opt id ctx.kid_id_renames_rev with
    | Some kid -> KBindings.add kid None ctx.kid_id_renames
    | None -> ctx.kid_id_renames
  in
  {
    ctx with
    kid_id_renames = KBindings.add kid (Some id) kir;
    kid_id_renames_rev = Bindings.add id kid ctx.kid_id_renames_rev;
  }

let add_global_kid_id_rename (global : global_context) id kid =
  let kir =
    match Bindings.find_opt id global.kid_id_renames_rev with
    | Some kid -> KBindings.add kid None global.kid_id_renames
    | None -> global.kid_id_renames
  in
  {
    global with
    kid_id_renames = KBindings.add kid (Some id) kir;
    kid_id_renames_rev = Bindings.add id kid global.kid_id_renames_rev;
  }

let implicit_parens x = enclose (string "{") (string "}") x
let leftarrow = string "←"
let leftarrowdo = string "← do"

(* Lean tokens that cannot appear as an identifier. A Sail name that collides
   with one of these is suffixed with a prime, which Lean accepts as an
   ordinary identifier character. Names Sail itself reserves are listed too so
   that the set can be read against Lean's grammar rather than against Sail's
   lexer. *)
let lean_reserved_names =
  Util.StringSet.of_list
    [
      (* declaration and command keywords *)
      "abbrev";
      "alias";
      "attribute";
      "axiom";
      "class";
      "def";
      "deriving";
      "example";
      "extends";
      "inductive";
      "instance";
      "local";
      "macro";
      "macro_rules";
      "mutual";
      "namespace";
      "noncomputable";
      "notation";
      "opaque";
      "open";
      "partial";
      "private";
      "protected";
      "scoped";
      "section";
      "set_option";
      "structure";
      "syntax";
      "theorem";
      "universe";
      "unsafe";
      "variable";
      (* fixity keywords *)
      "infix";
      "infixl";
      "infixr";
      "postfix";
      "prefix";
      (* term and tactic keywords *)
      "at";
      "block";
      "break";
      "calc";
      "catch";
      "continue";
      "finally";
      "from";
      "fun";
      "have";
      "matches";
      "meta";
      "nofun";
      "nomatch";
      "rec";
      "show";
      "sorry";
      "suffices";
      "this";
      "unless";
      "using";
      "where";
      "with";
    ]

let rec fix_id name =
  match name with
  (* Lean keywords to avoid, to expand as needed *)
  | "_lean_wildcard" -> "_"
  | _ when Util.StringSet.mem name lean_reserved_names -> name ^ "'"
  | "main" ->
      the_main_function_has_been_seen := true;
      "sail_main"
  | "?" -> "questionMark"
  | _ -> if String.contains name '#' then fix_id (String.concat "_" (String.split_on_char '#' name)) else name

let doc_id_ctor (Id_aux (i, _)) =
  match i with
  | And_bool -> string "and_bool"
  | Or_bool -> string "or_bool"
  | Id i -> string (fix_id i)
  | Operator x -> string (Util.zencode_string ("op " ^ x))

let doc_kid ctx (Kid_aux (Var x, _) as ki) =
  match KBindings.find_opt ki ctx.kid_docs with
  | Some doc -> doc
  | None -> (
      let ki =
        if
          KidSet.mem ki ctx.lean_bound_nvars
          || match KBindings.find_opt ki ctx.kid_id_renames with Some (Some _) -> true | _ -> false
        then ki
        else (
          let equal_bound =
            KidSet.inter (Spec_analysis.equal_kids ctx.env ki) ctx.lean_bound_nvars |> KidSet.elements
          in
          match equal_bound with equal_kid :: _ -> equal_kid | [] -> ki
        )
      in
      let (Kid_aux (Var x, _)) = ki in
      match KBindings.find_opt ki ctx.kid_id_renames with
      | Some (Some i) -> doc_id_ctor i
      | _ -> "k_" ^ String.sub x 1 (String.length x - 1) |> fix_id |> string
    )

let id_has_name name id = String.equal name (string_of_id id)

let prop_dependent_record id =
  List.exists (fun (record, _) -> id_has_name record id) !opt_prop_dependent_types
  || List.exists (fun record -> id_has_name record id) !inferred_prop_dependent_records

let prop_dependent_alias id = List.exists (fun (_, alias) -> id_has_name alias id) !opt_prop_dependent_types

let prop_dependent_record_for_alias id =
  List.find_map
    (fun (record, alias) -> if id_has_name alias id then Some (mk_id record) else None)
    !opt_prop_dependent_types

let prop_dependent_alias_typ = function
  | Typ_aux (Typ_id id, _) | Typ_aux (Typ_app (id, _), _) -> prop_dependent_alias id
  | _ -> false

let prop_dependent_record_typ = function
  | Typ_aux (Typ_id id, _) | Typ_aux (Typ_app (id, _), _) -> prop_dependent_record id
  | _ -> false

let prop_dependent_record_id_for_typ = function
  | (Typ_aux (Typ_id id, _) | Typ_aux (Typ_app (id, _), _)) when prop_dependent_record id -> Some id
  | _ -> None

let prop_dependent_record_application = function
  | Typ_aux (Typ_app (id, args), _) when prop_dependent_record id && args <> [] -> Some (id, args)
  | _ -> None

(* TODO do a proper renaming and keep track of it *)

let is_enum env id = match Env.lookup_id id env with Enum _ -> true | _ -> false

let pat_is_plain_binder ?(suffix = "") env (P_aux (p, _)) =
  match p with
  | P_id id when not (is_enum env id) -> Some (Some id, None)
  | P_id _ -> Some (Some (Id_aux (Id ("id" ^ suffix), Unknown)), None)
  | P_typ (typ, P_aux (P_id id, _)) when not (is_enum env id) -> Some (Some id, Some typ)
  | P_wild | P_typ (_, P_aux (P_wild, _)) -> Some (None, None)
  | P_var (_, _) -> Some (Some (Id_aux (Id ("var" ^ suffix), Unknown)), None)
  | P_app (_, _) -> Some (Some (Id_aux (Id ("app" ^ suffix), Unknown)), None)
  | P_vector _ -> Some (Some (Id_aux (Id ("vect" ^ suffix), Unknown)), None)
  | P_tuple _ -> Some (Some (Id_aux (Id ("tuple" ^ suffix), Unknown)), None)
  | P_list _ -> Some (Some (Id_aux (Id ("list" ^ suffix), Unknown)), None)
  | P_cons (_, _) -> Some (Some (Id_aux (Id ("cons" ^ suffix), Unknown)), None)
  | P_lit (L_aux (L_unit, _)) -> Some (Some (Id_aux (Id "_", Unknown)), None)
  | P_lit _ -> Some (Some (Id_aux (Id ("lit" ^ suffix), Unknown)), None)
  | P_typ _ -> Some (Some (Id_aux (Id ("typ" ^ suffix), Unknown)), None)
  | P_struct _ -> Some (Some (Id_aux (Id ("struct_pat" ^ suffix), Unknown)), None)
  | _ -> None

(* Copied from the Coq PP *)
let args_of_typ l env typs =
  let arg i typ =
    let id = mk_id ("arg" ^ string_of_int i) in
    ((P_aux (P_id id, (l, mk_tannot env typ)), typ), E_aux (E_id id, (l, mk_tannot env typ)))
  in
  List.split (List.mapi arg typs)

(* Copied from the Coq PP *)
(* Sail currently has a single pattern to match against a list of
   argument types.  We need to tweak everything to match up,
   especially so that the function is presented in curried form.  In
   particular, if there's a single binder for multiple arguments
   (which rewriting can currently introduce) then we need to turn it
   into multiple binders and reconstruct it in the function body using
   the second return value of this function. *)
let rec untuple_args_pat typs (P_aux (paux, ((l, _) as annot)) as pat) =
  let env = env_of_annot annot in
  let identity body = body in
  match (paux, typs) with
  | P_tuple [], _ | P_lit (L_aux (L_unit, _)), _ ->
      let annot = (l, mk_tannot Env.empty unit_typ) in
      ([(P_aux (P_lit (mk_lit L_unit), annot), unit_typ)], identity)
  (* The type checker currently has a special case for a single arg type; if
     that is removed, then remove the next case. *)
  | P_tuple pats, [typ] -> ([(pat, typ)], identity)
  | P_tuple pats, _ -> (List.combine pats typs, identity)
  | P_wild, _ ->
      let wild typ = (P_aux (P_wild, (l, mk_tannot env typ)), typ) in
      (List.map wild typs, identity)
  | P_typ (_, pat), _ -> untuple_args_pat typs pat
  | P_as _, _ :: _ :: _ | P_id _, _ :: _ :: _ ->
      let argpats, argexps = args_of_typ l env typs in
      let argexp = E_aux (E_tuple argexps, annot) in
      let bindargs (E_aux (_, bannot) as body) = E_aux (E_let (pat, argexp, body), bannot) in
      (argpats, bindargs)
  | _, [typ] -> ([(pat, typ)], identity)
  | _, _ -> unreachable l __POS__ "Unexpected pattern/type combination"

let string_of_nexp_con (Nexp_aux (n, l)) =
  match n with
  | Nexp_constant _ -> "NExp_constant"
  | Nexp_id _ -> "Nexp_id"
  | Nexp_var _ -> "Nexp_var"
  | Nexp_app _ -> "Nexp_app"
  | Nexp_if _ -> "Nexp_if"
  | Nexp_times _ -> "Nexp_times"
  | Nexp_sum _ -> "Nexp_sum"
  | Nexp_minus _ -> "Nexp_minus"
  | Nexp_neg _ -> "Nexp_neg"
  | Nexp_exp _ -> "Nexp_exp"

let string_of_typ_con (Typ_aux (t, _)) =
  match t with
  | Typ_app _ -> "Typ_app"
  | Typ_var _ -> "Typ_var"
  | Typ_fn _ -> "Typ_fn"
  | Typ_tuple _ -> "Typ_tuple"
  | Typ_exist _ -> "Typ_exist"
  | Typ_bidir _ -> "Typ_bidir"
  | Typ_internal_unknown -> "Typ_internal_unknown"
  | Typ_id _ -> "Typ_id"

let doc_big_int i = if i >= Z.zero then string (Big_int.to_string i) else parens (string (Big_int.to_string i))

let is_unit t = match t with Typ_aux (Typ_id (Id_aux (Id "unit", _)), _) -> true | _ -> false

let is_lit e lit = match e with E_aux (E_lit (L_aux (lit', _)), _) -> lit = lit' | _ -> false

let is_true e = is_lit e L_true
let is_false e = is_lit e L_false

(* Return the numeric variables that remain visible in the generated Lean type.
   Sail singleton integers and ranges are represented by Lean Nat/Int unless
   they are wrapped in a named semantic range type, so their indices must not
   create spurious Sigma components. *)
let rec lean_nvars_of_typ (Typ_aux (typ, _)) =
  match typ with
  | Typ_id _ -> KidSet.empty
  | Typ_var kid -> KidSet.singleton kid
  | Typ_fn (args, ret) ->
      List.fold_left (fun kids typ -> KidSet.union kids (lean_nvars_of_typ typ)) (lean_nvars_of_typ ret) args
  | Typ_tuple typs -> List.fold_left (fun kids typ -> KidSet.union kids (lean_nvars_of_typ typ)) KidSet.empty typs
  | Typ_app (Id_aux (Id ("implicit" | "range" | "atom" | "atom_bool"), _), _) -> KidSet.empty
  | Typ_app (_, args) ->
      List.fold_left (fun kids arg -> KidSet.union kids (lean_nvars_of_typ_arg arg)) KidSet.empty args
  | Typ_exist (kopts, _, inner) ->
      List.fold_left (fun kids kopt -> KidSet.remove (kopt_kid kopt) kids) (lean_nvars_of_typ inner) kopts
  | Typ_bidir _ | Typ_internal_unknown -> KidSet.empty

and lean_nvars_of_typ_arg (A_aux (arg, _)) =
  match arg with
  | A_nexp nexp -> tyvars_of_nexp nexp
  | A_typ typ -> lean_nvars_of_typ typ
  | A_bool nc -> tyvars_of_constraint nc

let relevant_existential_kopts kopts typ =
  let used = lean_nvars_of_typ typ in
  List.filter (fun kopt -> KidSet.mem (kopt_kid kopt) used) kopts

(* Adapted from Coq PP *)
let rec doc_nexp ctx (Nexp_aux (n, l) as nexp) =
  let rec plussub (Nexp_aux (n, l) as nexp) =
    match n with
    | Nexp_sum (n1, n2) -> separate space [plussub n1; plus; mul n2]
    | Nexp_minus (n1, n2) -> separate space [plussub n1; minus; mul n2]
    | _ -> mul nexp
  and mul (Nexp_aux (n, l) as nexp) =
    match n with Nexp_times (n1, n2) -> separate space [mul n1; star; uneg n2] | _ -> uneg nexp
  and uneg (Nexp_aux (n, l) as nexp) =
    match n with Nexp_neg n -> parens (separate space [minus; uneg n]) | _ -> exp nexp
  and exp (Nexp_aux (n, l) as nexp) =
    match n with Nexp_exp n -> separate space [string "2"; caret; exp n] | _ -> app nexp
  and app (Nexp_aux (n, l) as nexp) =
    match n with
    | Nexp_if (i, t, e) ->
        separate space [string "if ("; doc_nconstraint ctx i; string " : Bool) then"; atomic t; string "else"; atomic e]
    | Nexp_app (Id_aux (Id "div", _), [n1; n2]) -> separate space [atomic n1; string "/"; atomic n2]
    | Nexp_app (Id_aux (Id "mod", _), [n1; n2]) -> separate space [atomic n1; string "%"; atomic n2]
    | Nexp_app (Id_aux (Id "abs", _), [n1]) -> separate dot [atomic n1; string "natAbs"]
    | _ -> atomic nexp
  and atomic (Nexp_aux (n, l) as nexp) =
    match n with
    | Nexp_constant i -> doc_big_int i
    | Nexp_var ki -> doc_kid ctx ki
    | Nexp_id id -> doc_id_ctor id
    | Nexp_sum _ | Nexp_minus _ | Nexp_times _ | Nexp_neg _ | Nexp_exp _ | Nexp_if _
    | Nexp_app (Id_aux (Id ("div" | "mod"), _), [_; _])
    | Nexp_app (Id_aux (Id "abs", _), [_]) ->
        parens (plussub nexp)
    | _ -> failwith ("NExp " ^ string_of_nexp_con nexp ^ " " ^ string_of_nexp nexp ^ " not translatable yet.")
  in
  atomic nexp

and doc_nconstraint ctx (NC_aux (nc, _)) =
  match nc with
  | NC_and (n1, n2) -> flow (break 1) [doc_nconstraint ctx n1; string "∧"; doc_nconstraint ctx n2]
  | NC_or (n1, n2) -> flow (break 1) [doc_nconstraint ctx n1; string "∨"; doc_nconstraint ctx n2]
  | NC_equal (a1, a2) -> flow (break 1) [doc_typ_arg ctx `All a1; string "="; doc_typ_arg ctx `All a2]
  | NC_not_equal (a1, a2) -> flow (break 1) [doc_typ_arg ctx `All a1; string "≠"; doc_typ_arg ctx `All a2]
  | NC_app (f, args) -> parens (flow space (doc_id_ctor f :: List.map (doc_typ_arg ctx `All) args))
  | NC_false -> string "false"
  | NC_true -> string "true"
  | NC_ge (n1, n2) -> flow (break 1) [doc_nexp ctx n1; string "≥"; doc_nexp ctx n2]
  | NC_le (n1, n2) -> flow (break 1) [doc_nexp ctx n1; string "≤"; doc_nexp ctx n2]
  | NC_gt (n1, n2) -> flow (break 1) [doc_nexp ctx n1; string ">"; doc_nexp ctx n2]
  | NC_lt (n1, n2) -> flow (break 1) [doc_nexp ctx n1; string "<"; doc_nexp ctx n2]
  | NC_id i -> doc_id_ctor i
  | NC_set (n, vs) ->
      flow (break 1)
        [
          doc_nexp ctx n;
          string "∈";
          implicit_parens (separate_map comma_sp (fun x -> string (Nat_big_num.to_string x)) vs);
        ]
  | NC_var ki -> doc_kid ctx ki

and doc_typ_arg ctx rel (A_aux (t, _)) =
  match t with
  | A_typ t -> doc_typ ctx t
  | A_nexp n -> doc_nexp ctx n
  | A_bool nc -> (
      match rel with `Only_relevant -> empty | `All -> parens (doc_nconstraint ctx nc)
    )

and provably_nneg ctx x = Type_check.prove __POS__ ctx.env (nc_gteq x (nint 0))

and doc_typ ctx (Typ_aux (t, l) as typ) =
  match t with
  | Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp m, _); A_aux (A_typ elem_typ, _)]) ->
      (* TODO: remove duplication with exists, below *)
      nest 2 (parens (flow space [string "Vector"; doc_typ ctx elem_typ; doc_nexp ctx m]))
  | Typ_id (Id_aux (Id "unit", _)) -> string "Unit"
  | Typ_id (Id_aux (Id "int", _)) -> string "Int"
  | Typ_id (Id_aux (Id "string", _)) -> string "String"
  | Typ_app (Id_aux (Id "atom_bool", _), _) | Typ_id (Id_aux (Id "bool", _)) -> string "Bool"
  | Typ_id (Id_aux (Id "bit", _)) -> parens (string "BitVec 1")
  | Typ_id (Id_aux (Id "nat", _)) -> string "Nat"
  | Typ_app (Id_aux (Id "bitvector", _), [A_aux (A_nexp m, _)]) | Typ_app (Id_aux (Id "bits", _), [A_aux (A_nexp m, _)])
    ->
      parens (string "BitVec " ^^ doc_nexp ctx m)
  | Typ_app (Id_aux (Id "atom", _), [A_aux (A_nexp x, _)]) -> if provably_nneg ctx x then string "Nat" else string "Int"
  | Typ_app (Id_aux (Id "register", _), t_app) ->
      parens (string "RegisterRef " ^^ separate_map comma (doc_typ_app ctx) t_app)
  | Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]) ->
      underscore (* TODO check if the type of implicit arguments can really be always inferred *)
  | Typ_app (Id_aux (Id "option", _), [A_aux (A_typ typ, _)]) -> parens (string "Option " ^^ doc_typ ctx typ)
  | Typ_app (Id_aux (Id "list", _), args) ->
      parens (string "List" ^^ space ^^ separate_map space (doc_typ_arg ctx `Only_relevant) args)
  | Typ_tuple ts -> parens (separate_map (space ^^ string "×" ^^ space) (doc_typ ctx) ts)
  | Typ_id id -> doc_id_ctor id
  | Typ_app (id, _) when prop_dependent_record id -> doc_id_ctor id
  | Typ_app (Id_aux (Id "range", _), [A_aux (A_nexp low, _); A_aux (A_nexp high, _)]) ->
      if provably_nneg ctx low then string "Nat" else string "Int"
  | Typ_app (Id_aux (Id "result", _), [A_aux (A_typ typ1, _); A_aux (A_typ typ2, _)]) ->
      parens (separate space [string "Result"; doc_typ ctx typ1; doc_typ ctx typ2])
  | Typ_var kid -> doc_kid ctx kid
  | Typ_app (id, args) -> parens (doc_id_ctor id ^^ space ^^ separate_map space (doc_typ_arg ctx `Only_relevant) args)
  | Typ_exist (kopts, nc, typ) ->
      let env = List.fold_left (fun env kopt -> Env.add_typ_var l kopt env) ctx.env kopts in
      let env =
        try Env.add_constraint nc env
        with Type_internal.Type_error _ ->
          failwith
            ("Lean backend could not establish existential constraint " ^ string_of_n_constraint nc
           ^ " while rendering " ^ string_of_typ typ
            )
      in
      let ctx = context_with_env ctx env in
      let inner = doc_typ ctx typ in
      let relevant_kopts = relevant_existential_kopts kopts typ in
      if relevant_kopts <> [] then dependent_pair_instances_required := true;
      List.fold_right
        (fun (KOpt_aux (KOpt_kind (kind, kid), _)) inner ->
          parens
            (flow (break 1)
               [
                 string "Sigma";
                 string "fun";
                 parens (separate space [doc_kid ctx kid; colon; doc_existential_kind ctx kid kind]);
                 string "=>";
                 inner;
               ]
            )
        )
        relevant_kopts inner
  | _ -> failwith ("Type " ^ string_of_typ_con typ ^ " " ^ string_of_typ typ ^ " not translatable yet.")

and doc_typ_app ctx (A_aux (t, _) as typ) =
  match t with A_typ t' -> doc_typ ctx t' | A_bool nc -> doc_nconstraint ctx nc | A_nexp m -> doc_nexp ctx m

and doc_existential_kind ctx kid (K_aux (kind, _)) =
  match kind with
  | K_int -> if provably_nneg ctx (Nexp_aux (Nexp_var kid, Unknown)) then string "Nat" else string "Int"
  | K_bool -> string "Bool"
  | K_type -> string "Type"

let expand_synonyms_for_dependent_type ctx typ =
  try Env.expand_synonyms ctx.env typ
  with Type_internal.Type_error _ -> (
    match typ with
    | Typ_aux (Typ_id id, _) | Typ_aux (Typ_app (id, _), _) ->
        Option.value ~default:typ (Bindings.find_opt id ctx.global.semantic_types.aliases)
    | _ -> typ
  )

let dependent_types_equivalent ctx left right =
  try
    Type_check.alpha_equivalent ctx.env
      (expand_synonyms_for_dependent_type ctx left)
      (expand_synonyms_for_dependent_type ctx right)
  with Type_internal.Type_error _ -> false

(* Sail's flow typing refines type indices inside a branch, so a value whose
   own type mentions concrete indices can be accepted where the branch result
   type mentions the tested variable. Lean learns nothing from the Bool test,
   so the two record applications stay distinct types there and the value has
   to be cast under the branch hypothesis. Only record applications whose
   arguments are all indices qualify: their Lean parameters carry no data, and
   any genuine type argument would need a coercion of its own. *)
let index_refined_record_typ ctx expected actual =
  let expected = expand_synonyms_for_dependent_type ctx expected in
  let actual = expand_synonyms_for_dependent_type ctx actual in
  let all_index_args args = List.for_all (function A_aux (A_nexp _, _) -> true | _ -> false) args in
  match (expected, actual) with
  | Typ_aux (Typ_app (expected_id, expected_args), _), Typ_aux (Typ_app (actual_id, actual_args), _) ->
      Id.compare expected_id actual_id = 0
      && Bindings.mem expected_id ctx.global.semantic_types.record_fields
      && expected_args <> [] && all_index_args expected_args && all_index_args actual_args
      && not (dependent_types_equivalent ctx expected actual)
  | _ -> false

(* One ladder discharges every obligation this backend introduces: the equality
   between two record applications whose indices a branch refined, and the
   validity constraint carried by a constrained record or function signature.
   Both are linear arithmetic over the indices once the index projections and
   the branch hypotheses have been unfolded, which is what [simp_all] does. *)
let lean_discharge_tactic =
  "first | rfl | omega | (congr 1 <;> simp_all) | (congr 1 <;> omega) | (simp_all <;> omega) | (simp_all <;> rfl) | \
   simp_all"

let doc_discharge_by = string ("by " ^ lean_discharge_tactic)

(* The equality between the two record applications follows from the branch
   hypothesis, which Lean has in scope as a Bool equation. *)
let doc_index_refinement_cast value = parens (string "cast (" ^^ doc_discharge_by ^^ string ") " ^^ parens value)

(* Packing a value into an existential only needs a cast when the expected
   carrier fixes an index that the value's own type spells differently.  Index
   positions filled by the existential's own witnesses are solved by
   unification and must not be compared. *)
let existential_pack_refines_index ctx expected actual =
  match expand_synonyms_for_dependent_type ctx expected with
  | Typ_aux (Typ_exist (kopts, _, inner), _) -> (
      let bound = KidSet.of_list (List.map kopt_kid kopts) in
      match (expand_synonyms_for_dependent_type ctx inner, expand_synonyms_for_dependent_type ctx actual) with
      | Typ_aux (Typ_app (expected_id, expected_args), _), Typ_aux (Typ_app (actual_id, actual_args), _)
        when Id.compare expected_id actual_id = 0
             && Bindings.mem expected_id ctx.global.semantic_types.record_fields
             && List.length expected_args = List.length actual_args ->
          List.exists2
            (fun expected_arg actual_arg ->
              match (expected_arg, actual_arg) with
              | A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _), _ when KidSet.mem kid bound -> false
              | A_aux (A_nexp expected_nexp, _), A_aux (A_nexp actual_nexp, _) ->
                  not (nexp_identical expected_nexp actual_nexp)
              | A_aux (A_nexp _, _), _ -> true
              | _ -> false
            )
            expected_args actual_args
      | _ -> false
    )
  | _ -> false

(* An ascribed expression is always emitted at the ascribed type, packing its
   carrier on the way if that is what the ascription demands. A caller holding
   the same target must therefore not pack the result a second time. *)
let exp_is_ascribed_at ctx typ (E_aux (exp, _)) =
  match exp with E_typ (ascribed, _) -> dependent_types_equivalent ctx ascribed typ | _ -> false

let prop_dependent_alias_id_for_typ ctx typ =
  match typ with
  | (Typ_aux (Typ_id id, _) | Typ_aux (Typ_app (id, _), _)) when prop_dependent_alias id -> Some id
  | _ ->
      let expanded = expand_synonyms_for_dependent_type ctx typ in
      List.find_map
        (fun (_, alias_name) ->
          let alias = mk_id alias_name in
          match Bindings.find_opt alias ctx.global.semantic_types.aliases with
          | Some alias_typ -> (
              try
                if Type_check.alpha_equivalent ctx.env expanded (expand_synonyms_for_dependent_type ctx alias_typ) then
                  Some alias
                else None
              with Type_internal.Type_error _ -> None
            )
          | None -> None
        )
        !opt_prop_dependent_types

let prop_dependent_alias_for_typ ctx typ = Option.is_some (prop_dependent_alias_id_for_typ ctx typ)

let rec has_dependent_type ctx typ =
  if prop_dependent_record_typ typ then true
  else (
    let typ = expand_synonyms_for_dependent_type ctx typ in
    if prop_dependent_record_typ typ then true
    else (
      match typ with
      | Typ_aux (Typ_exist (kopts, _, inner), _) ->
          relevant_existential_kopts kopts inner <> [] || has_dependent_type ctx inner
      | Typ_aux (Typ_app (_, args), _) ->
          List.exists (function A_aux (A_typ inner, _) -> has_dependent_type ctx inner | _ -> false) args
      | Typ_aux (Typ_tuple typs, _) -> List.exists (has_dependent_type ctx) typs
      | _ -> false
    )
  )

let has_top_level_dependent_type ctx typ =
  if prop_dependent_record_typ typ then true
  else (
    let typ = expand_synonyms_for_dependent_type ctx typ in
    if prop_dependent_record_typ typ then true
    else (
      match typ with
      | Typ_aux (Typ_exist (kopts, _, inner), _) -> relevant_existential_kopts kopts inner <> []
      | _ -> false
    )
  )

let dependent_lambda binder body = parens (string "fun " ^^ binder ^^ string " => " ^^ body)

let dependent_type_nvar_available ctx kid =
  KidSet.mem kid ctx.lean_bound_nvars
  || match KBindings.find_opt kid ctx.kid_id_renames with Some (Some _) -> true | _ -> false

let rec contains_prop_dependent_alias ctx typ =
  if prop_dependent_alias_for_typ ctx typ || prop_dependent_record_typ typ then true
  else (
    let typ = expand_synonyms_for_dependent_type ctx typ in
    if prop_dependent_record_typ typ then true
    else (
      match typ with
      | Typ_aux (Typ_exist (_, _, inner), _) -> contains_prop_dependent_alias ctx inner
      | Typ_aux (Typ_app (_, args), _) ->
          List.exists (function A_aux (A_typ inner, _) -> contains_prop_dependent_alias ctx inner | _ -> false) args
      | Typ_aux (Typ_tuple typs, _) -> List.exists (contains_prop_dependent_alias ctx) typs
      | _ -> false
    )
  )

let inferred_prop_dependent_alias_args ctx alias (Typ_aux (_, location) as typ) =
  match
    ( Bindings.find_opt alias ctx.global.semantic_types.aliases,
      Bindings.find_opt alias ctx.global.semantic_types.alias_quants
    )
  with
  | Some alias_body, Some quant -> (
      let kopts = quant_kopts quant in
      let goals = KidSet.of_list (List.map kopt_kid kopts) in
      let env =
        List.fold_left
          (fun env kopt -> try Env.add_typ_var location kopt env with Type_internal.Type_error _ -> env)
          ctx.env kopts
      in
      try
        let unifiers = Type_check.unify location env goals alias_body typ in
        Some (List.map (fun kopt -> KBindings.find (kopt_kid kopt) unifiers) kopts)
      with _ -> None
    )
  | _ -> None

let rec doc_dependent_shape ctx typ =
  match prop_dependent_alias_id_for_typ ctx typ with
  | Some alias -> (
      match typ with
      | Typ_aux (Typ_app (id, args), _) when Id.compare id alias = 0 && args <> [] ->
          parens (flow space (doc_id_ctor alias :: List.map (doc_typ_arg ctx `All) args))
      | _ -> (
          match inferred_prop_dependent_alias_args ctx alias typ with
          | Some args when args <> [] -> parens (flow space (doc_id_ctor alias :: List.map (doc_typ_arg ctx `All) args))
          | _ ->
              if
                match Sys.getenv_opt "SAIL_LEAN_DEPENDENT_DEBUG" with Some ("1" | "true" | "yes") -> true | _ -> false
              then
                Printf.eprintf "lean-dependent-alias: could not recover arguments for %s from %s\n%!"
                  (string_of_id alias) (string_of_typ typ);
              doc_id_ctor alias
        )
    )
  | None -> (
      match prop_dependent_record_application typ with
      | Some (record, args) ->
          parens (flow space ((doc_id_ctor record ^^ string ".Indexed") :: List.map (doc_typ_arg ctx `All) args))
      | None -> (
          match prop_dependent_record_id_for_typ typ with
          | Some record -> doc_id_ctor record ^^ string ".Refined"
          | None -> (
              let typ = expand_synonyms_for_dependent_type ctx typ in
              match prop_dependent_record_application typ with
              | Some (record, args) ->
                  parens (flow space ((doc_id_ctor record ^^ string ".Indexed") :: List.map (doc_typ_arg ctx `All) args))
              | None -> (
                  match prop_dependent_record_id_for_typ typ with
                  | Some record -> doc_id_ctor record ^^ string ".Refined"
                  | None -> (
                      match typ with
                      | Typ_aux (Typ_app (Id_aux (Id "option", _), [A_aux (A_typ inner, _)]), _)
                        when has_dependent_type ctx inner ->
                          parens (string "Option " ^^ doc_dependent_shape ctx inner)
                      | Typ_aux (Typ_app (Id_aux (Id "list", _), [A_aux (A_typ inner, _)]), _)
                        when has_dependent_type ctx inner ->
                          parens (string "List " ^^ doc_dependent_shape ctx inner)
                      | Typ_aux
                          (Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp length, _); A_aux (A_typ inner, _)]), _)
                        when has_dependent_type ctx inner ->
                          nest 2
                            (parens (flow space [string "Vector"; doc_dependent_shape ctx inner; doc_nexp ctx length]))
                      | Typ_aux (Typ_tuple typs, _) when List.exists (has_dependent_type ctx) typs ->
                          parens (separate_map (space ^^ string "×" ^^ space) (doc_dependent_shape ctx) typs)
                      | Typ_aux (Typ_exist (kopts, nc, inner), l) ->
                          let env = List.fold_left (fun env kopt -> Env.add_typ_var l kopt env) ctx.env kopts in
                          let env = try Env.add_constraint nc env with Type_internal.Type_error _ -> env in
                          let ctx = context_with_env ctx env in
                          let relevant_kopts = relevant_existential_kopts kopts inner in
                          let ctx =
                            {
                              ctx with
                              lean_bound_nvars =
                                List.fold_left
                                  (fun bound kopt -> KidSet.add (kopt_kid kopt) bound)
                                  ctx.lean_bound_nvars relevant_kopts;
                            }
                          in
                          List.fold_right
                            (fun (KOpt_aux (KOpt_kind (kind, kid), _)) body ->
                              parens
                                (flow (break 1)
                                   [
                                     string "Sigma";
                                     string "fun";
                                     parens (separate space [doc_kid ctx kid; colon; doc_existential_kind ctx kid kind]);
                                     string "=>";
                                     body;
                                   ]
                                )
                            )
                            relevant_kopts (doc_typ ctx inner)
                      | _ -> doc_typ ctx typ
                    )
                )
            )
        )
    )

let doc_dependent_pattern ?(proof = string "_sailValidity") ctx typ pattern =
  if prop_dependent_alias_for_typ ctx typ then string "⟨" ^^ pattern ^^ comma_sp ^^ proof ^^ string "⟩"
  else if prop_dependent_record_typ typ then string "⟨" ^^ pattern ^^ comma_sp ^^ proof ^^ string "⟩"
  else (
    let typ = expand_synonyms_for_dependent_type ctx typ in
    match typ with
    | Typ_aux (Typ_exist (kopts, _, inner), _) ->
        List.fold_right
          (fun _ pattern -> string "⟨_, " ^^ pattern ^^ string "⟩")
          (relevant_existential_kopts kopts inner)
          pattern
    | _ -> pattern
  )

let rec constraint_application_ids (NC_aux (nc, _)) =
  match nc with
  | NC_app (id, _) -> IdSet.singleton id
  | NC_and (left, right) | NC_or (left, right) ->
      IdSet.union (constraint_application_ids left) (constraint_application_ids right)
  | _ -> IdSet.empty

let typquant_constraint_application_ids tq =
  List.fold_left
    (fun ids (QI_aux (item, _)) ->
      match item with QI_constraint constraint_ -> IdSet.union ids (constraint_application_ids constraint_) | _ -> ids
    )
    IdSet.empty tq

let instantiate_constraint instantiation nc =
  KBindings.fold (fun kid arg nc -> Ast_util.constraint_subst kid arg nc) instantiation nc

let rec prop_dependent_carrier_record_ids ctx typ =
  match prop_dependent_record_id_for_typ typ with
  | Some record -> IdSet.singleton record
  | None ->
      let expanded = expand_synonyms_for_dependent_type ctx typ in
      if Typ.compare expanded typ <> 0 then prop_dependent_carrier_record_ids ctx expanded
      else (
        match expanded with
        | Typ_aux (Typ_tuple typs, _) ->
            List.fold_left
              (fun records typ -> IdSet.union records (prop_dependent_carrier_record_ids ctx typ))
              IdSet.empty typs
        | _ -> IdSet.empty
      )

let rec prop_dependent_carrier_properties ctx root typ =
  match prop_dependent_record_id_for_typ typ with
  | Some _ -> [parens root ^^ string ".property"]
  | None ->
      let expanded = expand_synonyms_for_dependent_type ctx typ in
      if Typ.compare expanded typ <> 0 then prop_dependent_carrier_properties ctx root expanded
      else (
        match expanded with
        | Typ_aux (Typ_tuple typs, _) ->
            let rec collect root = function
              | [] -> []
              | [typ] -> prop_dependent_carrier_properties ctx root typ
              | typ :: rest ->
                  prop_dependent_carrier_properties ctx (parens root ^^ string ".1") typ
                  @ collect (parens root ^^ string ".2") rest
            in
            collect root typs
        | _ -> []
      )

let prop_dependent_result_proof ctx result =
  let unfold =
    string (result.result_name ^ ".Valid")
    :: List.concat_map
         (fun record -> [doc_id_ctor record ^^ string ".Indexed.Valid"; doc_id_ctor record ^^ string ".Valid"])
         (IdSet.elements (prop_dependent_carrier_record_ids ctx result.result_carrier))
    @ List.map doc_id_ctor (IdSet.elements (constraint_application_ids result.result_constraint))
  in
  let properties =
    List.mapi
      (fun index property -> string (Printf.sprintf "have resultValidity%i := " index) ^^ property)
      (prop_dependent_carrier_properties ctx (string "resultCarrier") result.result_carrier)
  in
  let source_properties =
    List.mapi
      (fun index property -> string (Printf.sprintf "have sourceValidity%i := " index) ^^ property)
      (prop_dependent_carrier_properties ctx (string "dependentResult") result.result_carrier)
  in
  string "by"
  ^^ nest 2
       (hardline
       ^^ separate hardline
            (source_properties @ properties
            @ [string "simp_all [" ^^ separate comma_sp unfold ^^ string "] <;> first | omega | grind"]
            )
       )

let prop_dependent_alias_parts ctx alias =
  match Bindings.find_opt alias ctx.global.semantic_types.aliases with
  | Some (Typ_aux (Typ_exist (_, nc, (Typ_aux (Typ_app (record, _), _) as inner)), _)) when prop_dependent_record record
    ->
      Some (record, nc, inner)
  | _ -> None

let context_dependent_validity ctx =
  let add_packed id typ (facts, unfold) =
    match prop_dependent_alias_id_for_typ ctx typ with
    | Some alias -> (
        match prop_dependent_alias_parts ctx alias with
        | Some (record, _, _) ->
            ( (string ("have dependentValidity_" ^ fix_id (string_of_id id) ^ " := ")
              ^^ parens (doc_id_ctor id)
              ^^ string ".property"
              )
              :: facts,
              (doc_id_ctor alias ^^ string ".Valid") :: (doc_id_ctor record ^^ string ".Valid") :: unfold
            )
        | None -> (facts, unfold)
      )
    | None -> (
        match prop_dependent_record_id_for_typ typ with
        | Some record ->
            ( (string ("have dependentValidity_" ^ fix_id (string_of_id id) ^ " := ")
              ^^ parens (doc_id_ctor id)
              ^^ string ".property"
              )
              :: facts,
              match prop_dependent_record_application typ with
              | Some _ ->
                  (doc_id_ctor record ^^ string ".Indexed.Valid") :: (doc_id_ctor record ^^ string ".Valid") :: unfold
              | None -> (doc_id_ctor record ^^ string ".Valid") :: unfold
            )
        | None -> (facts, unfold)
      )
  in
  let facts, unfold = Bindings.fold add_packed ctx.packed_dependent_types ([], []) in
  Bindings.fold
    (fun id result (facts, unfold) ->
      let root = parens (doc_id_ctor id) ^^ string ".val" in
      let result_facts =
        List.mapi
          (fun index property ->
            string (Printf.sprintf "have dependentResultValidity_%s_%i := " (fix_id (string_of_id id)) index)
            ^^ property
          )
          (prop_dependent_carrier_properties ctx root result.result_carrier)
      in
      ( (string ("have dependentResultValidity_" ^ fix_id (string_of_id id) ^ " := ")
        ^^ parens (doc_id_ctor id)
        ^^ string ".property"
        )
        :: result_facts
        @ facts,
        string (result.result_name ^ ".Valid")
        :: List.map
             (fun record -> doc_id_ctor record ^^ string ".Valid")
             (IdSet.elements (prop_dependent_carrier_record_ids ctx result.result_carrier))
        @ unfold
      )
    )
    ctx.packed_dependent_results (facts, unfold)

let doc_constraint_proof ?(facts = []) ?(extra_unfold = []) ctx nc =
  let context_facts, dependent_unfold = context_dependent_validity ctx in
  let facts = context_facts @ facts in
  let unfold =
    List.map doc_id_ctor (IdSet.elements (constraint_application_ids nc)) @ extra_unfold @ dependent_unfold
  in
  let tactic =
    match unfold with
    | [] -> string "first | omega | grind"
    | _ -> string "simp_all [" ^^ separate comma_sp unfold ^^ string "] <;> first | omega | grind"
  in
  if facts = [] then string "by " ^^ tactic else string "by" ^^ nest 2 (hardline ^^ separate hardline (facts @ [tactic]))

let prop_dependent_proof ?(facts = []) ctx typ =
  let context_facts, context_unfold = context_dependent_validity ctx in
  let facts = context_facts @ facts in
  match prop_dependent_alias_id_for_typ ctx typ with
  | Some alias -> (
      match prop_dependent_alias_parts ctx alias with
      | Some (record, nc, _) ->
          let unfold =
            IdSet.union (constraint_application_ids nc)
              ( match Bindings.find_opt record ctx.global.semantic_types.record_quants with
              | Some quant ->
                  List.fold_left
                    (fun ids (QI_aux (item, _)) ->
                      match item with QI_constraint nc -> IdSet.union ids (constraint_application_ids nc) | _ -> ids
                    )
                    IdSet.empty quant
              | None -> IdSet.empty
              )
          in
          let unfold =
            (doc_id_ctor alias ^^ string ".Valid")
            :: (doc_id_ctor record ^^ string ".Valid")
            :: List.map doc_id_ctor (IdSet.elements unfold)
            @ context_unfold
          in
          let tactic = string "simp_all [" ^^ separate comma_sp unfold ^^ string "] <;> first | omega | grind" in
          if facts = [] then string "by " ^^ tactic
          else string "by" ^^ nest 2 (hardline ^^ separate hardline (facts @ [tactic]))
      | None -> failwith ("No proof-refined carrier configured for " ^ string_of_id alias)
    )
  | None -> failwith ("Expected a named proof-refined alias, got " ^ string_of_typ typ)

let prop_dependent_record_proof ?(facts = []) ?(extra_unfold = []) ctx typ =
  let record =
    match prop_dependent_record_id_for_typ typ with
    | Some record -> record
    | None -> failwith ("Expected a proof-refined record, got " ^ string_of_typ typ)
  in
  let context_facts, context_unfold = context_dependent_validity ctx in
  let facts = context_facts @ facts in
  let unfold =
    match Bindings.find_opt record ctx.global.semantic_types.record_quants with
    | Some quant ->
        List.fold_left
          (fun ids (QI_aux (item, _)) ->
            match item with QI_constraint nc -> IdSet.union ids (constraint_application_ids nc) | _ -> ids
          )
          IdSet.empty quant
    | None -> IdSet.empty
  in
  let unfold =
    ( match prop_dependent_record_application typ with
      | Some _ -> [doc_id_ctor record ^^ string ".Indexed.Valid"; doc_id_ctor record ^^ string ".Valid"]
      | None -> [doc_id_ctor record ^^ string ".Valid"]
      )
    @ List.map doc_id_ctor (IdSet.elements unfold)
  in
  let unfold = unfold @ extra_unfold @ context_unfold in
  let tactic = string "simp_all [" ^^ separate comma_sp unfold ^^ string "] <;> first | omega | grind" in
  if facts = [] then string "by " ^^ tactic else string "by" ^^ nest 2 (hardline ^^ separate hardline (facts @ [tactic]))

let singleton_kid_of_field env typ =
  try
    match Env.expand_synonyms env typ with
    | Typ_aux (Typ_app (Id_aux (Id ("atom" | "implicit"), _), [A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _)]), _) ->
        Some kid
    | _ -> None
  with Type_internal.Type_error _ -> None

let quantified_int_kids tq =
  List.filter_map
    (fun (QI_aux (item, _)) ->
      match item with QI_id (KOpt_aux (KOpt_kind (K_aux (K_int, _), kid), _)) -> Some kid | _ -> None
    )
    tq

let doc_field_path root path = List.fold_left (fun doc field -> doc ^^ dot ^^ doc_id_ctor field) root path

let rec prop_dependent_record_declaration_witness_paths ctx seen record =
  if IdSet.mem record seen then KBindings.empty
  else (
    match
      ( Bindings.find_opt record ctx.global.semantic_types.record_quants,
        Bindings.find_opt record ctx.global.semantic_types.record_fields
      )
    with
    | Some quant, Some fields ->
        let seen = IdSet.add record seen in
        let field_env = Env.add_typquant Unknown quant ctx.env in
        Bindings.fold
          (fun field typ witnesses ->
            match singleton_kid_of_field field_env typ with
            | Some kid -> KBindings.add kid [field] witnesses
            | None -> (
                let typ = try Env.expand_synonyms field_env typ with Type_internal.Type_error _ -> typ in
                match typ with
                | Typ_aux (Typ_app (nested_record, args), _) when prop_dependent_record nested_record -> (
                    match Bindings.find_opt nested_record ctx.global.semantic_types.record_quants with
                    | Some nested_quant ->
                        let nested_kids = quantified_int_kids nested_quant in
                        let nested_paths = prop_dependent_record_declaration_witness_paths ctx seen nested_record in
                        let actuals = try List.combine nested_kids args with Invalid_argument _ -> [] in
                        List.fold_left
                          (fun witnesses (nested_kid, A_aux (arg, _)) ->
                            match (KBindings.find_opt nested_kid nested_paths, arg) with
                            | Some path, A_nexp (Nexp_aux (Nexp_var actual_kid, _)) ->
                                KBindings.add actual_kid (field :: path) witnesses
                            | _ -> witnesses
                          )
                          witnesses actuals
                    | None -> witnesses
                  )
                | _ -> witnesses
              )
          )
          fields KBindings.empty
    | _ -> KBindings.empty
  )

let rec prop_dependent_record_witness_paths ctx inner =
  match inner with
  | Typ_aux (Typ_app (record, args), _) when prop_dependent_record record -> (
      match Bindings.find_opt record ctx.global.semantic_types.record_quants with
      | Some quant ->
          let quantified =
            List.filter_map
              (fun (QI_aux (item, _)) ->
                match item with QI_id (KOpt_aux (KOpt_kind (kind, kid), _)) -> Some (kind, kid) | _ -> None
              )
              quant
          in
          let actuals = try List.combine quantified args with Invalid_argument _ -> [] in
          let declaration_paths = prop_dependent_record_declaration_witness_paths ctx IdSet.empty record in
          List.fold_left
            (fun witnesses ((kind, declaration_kid), A_aux (arg, _)) ->
              match (kind, arg, KBindings.find_opt declaration_kid declaration_paths) with
              | K_aux (K_int, _), A_nexp (Nexp_aux (Nexp_var actual_kid, _)), Some path ->
                  KBindings.add actual_kid path witnesses
              | _ -> witnesses
            )
            KBindings.empty actuals
      | _ -> KBindings.empty
    )
  | _ ->
      let expanded = expand_synonyms_for_dependent_type ctx inner in
      if Typ.compare expanded inner <> 0 then prop_dependent_record_witness_paths ctx expanded
      else (
        match expanded with
        | Typ_aux (Typ_exist (_, _, carrier), _) -> prop_dependent_record_witness_paths ctx carrier
        | _ -> KBindings.empty
      )

let merge_kbindings left right = KBindings.fold KBindings.add right left

let rec prop_dependent_carrier_witness_docs ctx root typ =
  match prop_dependent_record_id_for_typ typ with
  | Some _ -> KBindings.map (doc_field_path (parens root ^^ string ".val")) (prop_dependent_record_witness_paths ctx typ)
  | None ->
      let expanded = expand_synonyms_for_dependent_type ctx typ in
      if Typ.compare expanded typ <> 0 then prop_dependent_carrier_witness_docs ctx root expanded
      else (
        match expanded with
        | Typ_aux (Typ_tuple typs, _) ->
            let rec collect root = function
              | [] -> KBindings.empty
              | [typ] -> prop_dependent_carrier_witness_docs ctx root typ
              | typ :: rest ->
                  merge_kbindings
                    (prop_dependent_carrier_witness_docs ctx (parens root ^^ string ".1") typ)
                    (collect (parens root ^^ string ".2") rest)
            in
            collect root typs
        | _ -> KBindings.empty
      )

let rec prop_dependent_result_carrier_eligible ctx typ =
  match prop_dependent_record_id_for_typ typ with
  | Some _ -> true
  | None ->
      let expanded = expand_synonyms_for_dependent_type ctx typ in
      if Typ.compare expanded typ <> 0 then prop_dependent_result_carrier_eligible ctx expanded
      else (
        match expanded with
        | Typ_aux (Typ_tuple typs, _) -> typs <> [] && List.for_all (prop_dependent_result_carrier_eligible ctx) typs
        | _ -> false
      )

let infer_prop_dependent_result ctx id tq typ =
  match typ with
  | Typ_aux (Typ_exist (kopts, nc, carrier), _) when prop_dependent_result_carrier_eligible ctx carrier ->
      let relevant_kopts = relevant_existential_kopts kopts carrier in
      let witness_docs = prop_dependent_carrier_witness_docs ctx (string "value") carrier in
      let existential_kids = KidSet.of_list (List.map kopt_kid kopts) in
      let unrecoverable_existential_kids =
        KidSet.filter
          (fun kid -> not (KBindings.mem kid witness_docs))
          (KidSet.inter existential_kids (tyvars_of_constraint nc))
      in
      let parameter_kids =
        KidSet.filter
          (fun kid -> (not (KidSet.mem kid existential_kids)) && not (KBindings.mem kid witness_docs))
          (tyvars_of_constraint nc)
      in
      let result_params = List.filter (fun kopt -> KidSet.mem (kopt_kid kopt) parameter_kids) (quant_kopts tq) in
      if
        relevant_kopts <> []
        && KidSet.is_empty unrecoverable_existential_kids
        && List.for_all (fun (KOpt_aux (KOpt_kind (_, kid), _)) -> KBindings.mem kid witness_docs) relevant_kopts
        && List.length result_params = KidSet.cardinal parameter_kids
      then
        Some
          {
            result_name = Util.to_upper_camel_case (fix_id (string_of_id id)) ^ "Result";
            result_quant = tq;
            result_kopts = relevant_kopts;
            result_params;
            result_constraint = nc;
            result_carrier = carrier;
            result_typ = typ;
          }
      else None
  | _ -> None

let prop_dependent_result_for_id ctx id = Bindings.find_opt id ctx.global.prop_dependent_results

let doc_prop_dependent_result_type ctx result =
  match result.result_params with
  | [] -> string result.result_name
  | params ->
      parens
        (string result.result_name ^^ space
        ^^ separate_map space (fun (KOpt_aux (KOpt_kind (_, kid), _)) -> doc_kid ctx kid) params
        )

(* A result-specific [Valid] predicate already retains the relationships among
   existential witnesses.  Its carrier therefore needs only each record's
   base validity, not a second indexed wrapper whose indices would escape the
   result declaration. *)
let rec doc_prop_dependent_result_carrier_shape ctx typ =
  match prop_dependent_record_id_for_typ typ with
  | Some record -> doc_id_ctor record ^^ string ".Refined"
  | None ->
      let expanded = expand_synonyms_for_dependent_type ctx typ in
      if Typ.compare expanded typ <> 0 then doc_prop_dependent_result_carrier_shape ctx expanded
      else (
        match expanded with
        | Typ_aux (Typ_tuple typs, _) ->
            parens (separate_map (space ^^ string "×" ^^ space) (doc_prop_dependent_result_carrier_shape ctx) typs)
        | _ -> doc_dependent_shape ctx typ
      )

(* A result carrier deliberately erases each component's indices to the
   record's [Refined] form.  Reconstruct those indices in the aggregate
   validity predicate from the original carrier type.  This keeps all
   relationships in Prop while the runtime carrier remains the plain record
   values. *)
let rec doc_prop_dependent_result_carrier_validities ctx root typ =
  match prop_dependent_record_application typ with
  | Some (record, args) ->
      [
        parens
          (flow space
             (((doc_id_ctor record ^^ string ".Indexed.Valid") :: List.map (doc_typ_arg ctx `All) args)
             @ [parens root ^^ string ".val"]
             )
          );
      ]
  | None -> (
      match prop_dependent_record_id_for_typ typ with
      | Some record -> [parens (flow space [doc_id_ctor record ^^ string ".Valid"; parens root ^^ string ".val"])]
      | None ->
          let expanded = expand_synonyms_for_dependent_type ctx typ in
          if Typ.compare expanded typ <> 0 then doc_prop_dependent_result_carrier_validities ctx root expanded
          else (
            match expanded with
            | Typ_aux (Typ_tuple typs, _) ->
                let rec collect root = function
                  | [] -> []
                  | [typ] -> doc_prop_dependent_result_carrier_validities ctx root typ
                  | typ :: rest ->
                      doc_prop_dependent_result_carrier_validities ctx (parens root ^^ string ".1") typ
                      @ collect (parens root ^^ string ".2") rest
                in
                collect root typs
            | _ -> []
          )
    )

let add_prop_dependent_record_binder_kid_docs ctx binder typ =
  let witness_paths = prop_dependent_record_witness_paths ctx typ in
  let kid_docs =
    KBindings.fold (fun kid path docs -> KBindings.add kid (doc_field_path binder path) docs) witness_paths ctx.kid_docs
  in
  { ctx with kid_docs }

let prop_dependent_repack_target ctx binder target_typ =
  let carrier = parens binder ^^ string ".val" in
  let target_ctx = add_prop_dependent_record_binder_kid_docs ctx carrier target_typ in
  (target_ctx, doc_dependent_shape target_ctx target_typ)

let rec doc_dependent_pack ctx typ value =
  match prop_dependent_alias_id_for_typ ctx typ with
  | Some alias -> string "⟨" ^^ value ^^ comma_sp ^^ prop_dependent_proof ctx typ ^^ string "⟩"
  | None -> (
      match prop_dependent_record_id_for_typ typ with
      | Some _ -> string "⟨" ^^ value ^^ comma_sp ^^ prop_dependent_record_proof ctx typ ^^ string "⟩"
      | None ->
          let typ = expand_synonyms_for_dependent_type ctx typ in
          if prop_dependent_record_typ typ then
            string "⟨" ^^ value ^^ comma_sp ^^ prop_dependent_record_proof ctx typ ^^ string "⟩"
          else (
            match typ with
            | Typ_aux (Typ_exist (kopts, _, inner), _) ->
                let relevant_kopts = relevant_existential_kopts kopts inner in
                let witness_paths = prop_dependent_record_witness_paths ctx inner in
                if
                  relevant_kopts <> []
                  && List.for_all
                       (fun (KOpt_aux (KOpt_kind (_, kid), _)) -> KBindings.mem kid witness_paths)
                       relevant_kopts
                then (
                  let binder = string "dependentValue" in
                  let packed =
                    List.fold_right
                      (fun (KOpt_aux (KOpt_kind (_, kid), _)) packed ->
                        let path = KBindings.find kid witness_paths in
                        string "⟨" ^^ doc_field_path binder path ^^ comma_sp ^^ packed ^^ string "⟩"
                      )
                      relevant_kopts (doc_dependent_pack ctx inner binder)
                  in
                  parens (dependent_lambda binder packed ^^ space ^^ parens value)
                )
                else (
                  let value = doc_dependent_pack ctx inner value in
                  List.fold_right (fun _ value -> string "⟨_, " ^^ value ^^ string "⟩") relevant_kopts value
                )
            | Typ_aux (Typ_app (Id_aux (Id "option", _), [A_aux (A_typ inner, _)]), _) when has_dependent_type ctx inner
              ->
                parens
                  (string "Option.map "
                  ^^ dependent_lambda (string "dependentValue") (doc_dependent_pack ctx inner (string "dependentValue"))
                  ^^ space ^^ parens value
                  )
            | Typ_aux (Typ_app (Id_aux (Id "list", _), [A_aux (A_typ inner, _)]), _) when has_dependent_type ctx inner
              ->
                parens
                  (string "List.map "
                  ^^ dependent_lambda (string "dependentValue") (doc_dependent_pack ctx inner (string "dependentValue"))
                  ^^ space ^^ parens value
                  )
            | Typ_aux (Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp _, _); A_aux (A_typ inner, _)]), _)
              when has_dependent_type ctx inner ->
                parens
                  (string "Vector.map "
                  ^^ dependent_lambda (string "dependentValue") (doc_dependent_pack ctx inner (string "dependentValue"))
                  ^^ space ^^ parens value
                  )
            | Typ_aux (Typ_tuple typs, _) when List.exists (has_dependent_type ctx) typs ->
                let names = List.mapi (fun i _ -> Printf.sprintf "dependentValue%i" i) typs in
                let pat = parens (separate comma_sp (List.map string names)) in
                let body =
                  parens
                    (separate comma_sp (List.map2 (fun typ name -> doc_dependent_pack ctx typ (string name)) typs names))
                in
                parens (dependent_lambda pat body ^^ space ^^ parens value)
            | _ -> value
          )
    )

let rec doc_dependent_unpack ctx typ value =
  if prop_dependent_alias_for_typ ctx typ then parens value ^^ string ".val"
  else if prop_dependent_record_typ typ then parens value ^^ string ".val"
  else (
    let typ = expand_synonyms_for_dependent_type ctx typ in
    if prop_dependent_record_typ typ then parens value ^^ string ".val"
    else (
      match typ with
      | Typ_aux (Typ_exist (kopts, _, inner), _) ->
          let value =
            List.fold_left (fun value _ -> parens value ^^ string ".2") value (relevant_existential_kopts kopts inner)
          in
          doc_dependent_unpack ctx inner value
      | Typ_aux (Typ_app (Id_aux (Id "option", _), [A_aux (A_typ inner, _)]), _) when has_dependent_type ctx inner ->
          parens
            (string "Option.map "
            ^^ dependent_lambda (string "dependentValue") (doc_dependent_unpack ctx inner (string "dependentValue"))
            ^^ space ^^ parens value
            )
      | Typ_aux (Typ_app (Id_aux (Id "list", _), [A_aux (A_typ inner, _)]), _) when has_dependent_type ctx inner ->
          parens
            (string "List.map "
            ^^ dependent_lambda (string "dependentValue") (doc_dependent_unpack ctx inner (string "dependentValue"))
            ^^ space ^^ parens value
            )
      | Typ_aux (Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp _, _); A_aux (A_typ inner, _)]), _)
        when has_dependent_type ctx inner ->
          parens
            (string "Vector.map "
            ^^ dependent_lambda (string "dependentValue") (doc_dependent_unpack ctx inner (string "dependentValue"))
            ^^ space ^^ parens value
            )
      | Typ_aux (Typ_tuple typs, _) when List.exists (has_dependent_type ctx) typs ->
          let names = List.mapi (fun i _ -> Printf.sprintf "dependentValue%i" i) typs in
          let pat = parens (separate comma_sp (List.map string names)) in
          let body =
            parens
              (separate comma_sp (List.map2 (fun typ name -> doc_dependent_unpack ctx typ (string name)) typs names))
          in
          parens (dependent_lambda pat body ^^ space ^^ parens value)
      | _ -> value
    )
  )

let doc_dependent_repack ctx source_typ target_typ value =
  match (prop_dependent_record_id_for_typ source_typ, prop_dependent_alias_id_for_typ ctx target_typ) with
  | Some source_record, Some target_alias -> (
      match prop_dependent_alias_parts ctx target_alias with
      | Some (target_record, _, _) when Id.compare source_record target_record = 0 ->
          let binder = string "dependentValue" in
          let target_ctx, target_shape = prop_dependent_repack_target ctx binder target_typ in
          let proof =
            string "by" ^^ hardline ^^ string "   constructor" ^^ hardline ^^ string "   · exact "
            ^^ ( match prop_dependent_record_application source_typ with
              | Some _ -> string "dependentValue.property.1"
              | None -> string "dependentValue.property"
              )
            ^^ hardline ^^ string "   · exact "
            ^^ parens
                 (prop_dependent_proof
                    ~facts:[string "have dependentValidity := dependentValue.property"]
                    target_ctx target_typ
                 )
          in
          parens
            (string "let " ^^ binder ^^ string " := " ^^ parens value ^^ hardline
            ^^ parens
                 (separate space
                    [string "⟨" ^^ binder ^^ string ".val" ^^ comma_sp ^^ proof ^^ string "⟩"; colon; target_shape]
                 )
            )
      | _ -> doc_dependent_pack ctx target_typ (doc_dependent_unpack ctx source_typ value)
    )
  | Some source_record, None -> (
      match prop_dependent_record_id_for_typ target_typ with
      | Some target_record when Id.compare source_record target_record = 0 ->
          let binder = string "dependentValue" in
          let target_ctx, target_shape = prop_dependent_repack_target ctx binder target_typ in
          parens
            (string "let " ^^ binder ^^ string " := " ^^ parens value ^^ hardline
            ^^ parens
                 (separate space
                    [
                      string "⟨" ^^ binder ^^ string ".val" ^^ comma_sp
                      ^^ prop_dependent_record_proof
                           ~facts:[string "have dependentValidity := dependentValue.property"]
                           target_ctx target_typ
                      ^^ string "⟩";
                      colon;
                      target_shape;
                    ]
                 )
            )
      | _ -> doc_dependent_pack ctx target_typ (doc_dependent_unpack ctx source_typ value)
    )
  | None, None -> (
      match (prop_dependent_alias_id_for_typ ctx source_typ, prop_dependent_record_id_for_typ target_typ) with
      | Some source_alias, Some target_record -> (
          match prop_dependent_alias_parts ctx source_alias with
          | Some (source_record, _, _) when Id.compare source_record target_record = 0 ->
              let binder = string "dependentValue" in
              let target_ctx, target_shape = prop_dependent_repack_target ctx binder target_typ in
              parens
                (string "let " ^^ binder ^^ string " := " ^^ parens value ^^ hardline
                ^^ parens
                     (separate space
                        [
                          string "⟨" ^^ binder ^^ string ".val" ^^ comma_sp
                          ^^ prop_dependent_record_proof
                               ~facts:[string "have dependentValidity := dependentValue.property"]
                               target_ctx target_typ
                          ^^ string "⟩";
                          colon;
                          target_shape;
                        ]
                     )
                )
          | _ -> doc_dependent_pack ctx target_typ (doc_dependent_unpack ctx source_typ value)
        )
      | _ -> doc_dependent_pack ctx target_typ (doc_dependent_unpack ctx source_typ value)
    )
  | _ -> doc_dependent_pack ctx target_typ (doc_dependent_unpack ctx source_typ value)

let semantic_range_id ctx typ =
  let rec resolve seen = function
    | Typ_aux (Typ_id id, _) | Typ_aux (Typ_app (id, []), _) ->
        if Bindings.mem id ctx.global.semantic_types.ranges then Some id
        else if IdSet.mem id seen then None
        else (
          match Bindings.find_opt id ctx.global.semantic_types.aliases with
          | Some typ -> resolve (IdSet.add id seen) typ
          | None -> None
        )
    | _ -> None
  in
  resolve IdSet.empty typ

let rec has_semantic_range ctx (Typ_aux (t, _) as typ) =
  match semantic_range_id ctx typ with
  | Some _ -> true
  | None -> (
      match t with
      | Typ_app (_, args) ->
          List.exists (function A_aux (A_typ typ, _) -> has_semantic_range ctx typ | _ -> false) args
      | Typ_tuple typs -> List.exists (has_semantic_range ctx) typs
      | Typ_exist (_, _, typ) -> has_semantic_range ctx typ
      | Typ_fn (args, ret) -> List.exists (has_semantic_range ctx) args || has_semantic_range ctx ret
      | _ -> false
    )

let semantic_lambda binder body = parens (string "fun " ^^ binder ^^ string " => " ^^ body)

let rec doc_semantic_pack ctx typ value =
  match semantic_range_id ctx typ with
  | Some _ -> string "⟨" ^^ value ^^ string "⟩"
  | None -> (
      match typ with
      | Typ_aux (Typ_app (Id_aux (Id "option", _), [A_aux (A_typ inner, _)]), _) when has_semantic_range ctx inner ->
          parens
            (string "Option.map "
            ^^ semantic_lambda (string "semanticValue") (doc_semantic_pack ctx inner (string "semanticValue"))
            ^^ space ^^ parens value
            )
      | Typ_aux (Typ_app (Id_aux (Id "list", _), [A_aux (A_typ inner, _)]), _) when has_semantic_range ctx inner ->
          parens
            (string "List.map "
            ^^ semantic_lambda (string "semanticValue") (doc_semantic_pack ctx inner (string "semanticValue"))
            ^^ space ^^ parens value
            )
      | Typ_aux (Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp _, _); A_aux (A_typ inner, _)]), _)
        when has_semantic_range ctx inner ->
          parens
            (string "Vector.map "
            ^^ semantic_lambda (string "semanticValue") (doc_semantic_pack ctx inner (string "semanticValue"))
            ^^ space ^^ parens value
            )
      | Typ_aux (Typ_tuple typs, _) when List.exists (has_semantic_range ctx) typs ->
          let names = List.mapi (fun i _ -> Printf.sprintf "semanticValue%i" i) typs in
          let pat = parens (separate comma_sp (List.map string names)) in
          let body =
            parens (separate comma_sp (List.map2 (fun typ name -> doc_semantic_pack ctx typ (string name)) typs names))
          in
          parens (semantic_lambda pat body ^^ space ^^ parens value)
      | Typ_aux (Typ_exist (_, _, inner), _) -> doc_semantic_pack ctx inner value
      | _ -> value
    )

let rec doc_semantic_unpack ctx typ value =
  match semantic_range_id ctx typ with
  | Some _ -> parens value ^^ string ".value"
  | None -> (
      match typ with
      | Typ_aux (Typ_app (Id_aux (Id "option", _), [A_aux (A_typ inner, _)]), _) when has_semantic_range ctx inner ->
          parens
            (string "Option.map "
            ^^ semantic_lambda (string "semanticValue") (doc_semantic_unpack ctx inner (string "semanticValue"))
            ^^ space ^^ parens value
            )
      | Typ_aux (Typ_app (Id_aux (Id "list", _), [A_aux (A_typ inner, _)]), _) when has_semantic_range ctx inner ->
          parens
            (string "List.map "
            ^^ semantic_lambda (string "semanticValue") (doc_semantic_unpack ctx inner (string "semanticValue"))
            ^^ space ^^ parens value
            )
      | Typ_aux (Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp _, _); A_aux (A_typ inner, _)]), _)
        when has_semantic_range ctx inner ->
          parens
            (string "Vector.map "
            ^^ semantic_lambda (string "semanticValue") (doc_semantic_unpack ctx inner (string "semanticValue"))
            ^^ space ^^ parens value
            )
      | Typ_aux (Typ_tuple typs, _) when List.exists (has_semantic_range ctx) typs ->
          let names = List.mapi (fun i _ -> Printf.sprintf "semanticValue%i" i) typs in
          let pat = parens (separate comma_sp (List.map string names)) in
          let body =
            parens (separate comma_sp (List.map2 (fun typ name -> doc_semantic_unpack ctx typ (string name)) typs names))
          in
          parens (semantic_lambda pat body ^^ space ^^ parens value)
      | Typ_aux (Typ_exist (_, _, inner), _) -> doc_semantic_unpack ctx inner value
      | _ -> value
    )

let semantic_function_type ctx id =
  match Bindings.find_opt id ctx.global.semantic_types.valspecs with
  | Some (Typ_aux (Typ_fn (args, ret), _)) -> Some (args, ret)
  | _ -> None

let rec app_returns_prop_dependent_record ctx = function
  | E_aux (E_app (id, _), _) -> (
      match semantic_function_type ctx id with
      | Some (_, ret) -> prop_dependent_record_typ ret || prop_dependent_alias_for_typ ctx ret
      | None -> false
    )
  | E_aux (E_typ (_, expression), _) | E_aux (E_block [expression], _) ->
      app_returns_prop_dependent_record ctx expression
  | _ -> false

let rec prop_dependent_result_of_exp ctx = function
  | E_aux (E_app (id, _), _) -> prop_dependent_result_for_id ctx id
  | E_aux (E_id id, _) -> Bindings.find_opt id ctx.packed_dependent_results
  | E_aux (E_typ (_, exp), _) | E_aux (E_block [exp], _) -> prop_dependent_result_of_exp ctx exp
  | _ -> None

let rec expression_never_returns = function
  | E_aux ((E_exit _ | E_throw _), _) -> true
  | E_aux (E_typ (_, exp), _) | E_aux (E_block [exp], _) -> expression_never_returns exp
  | _ -> false

let rec expression_is_unit_value = function
  | E_aux (E_lit (L_aux (L_unit, _)), _) -> true
  | E_aux (E_typ (_, exp), _) | E_aux (E_block [exp], _) -> expression_is_unit_value exp
  | _ -> false

(* A global binding whose declared type packs existential indices is emitted
   already unpacked whenever the use site instantiated those indices, so the
   value that reaches the surrounding expression is the fields carrier rather
   than the packed Sigma. Both the emission in [doc_exp]'s [E_id] case and the
   representation predicates below must agree on that, otherwise the value is
   projected twice. *)
let global_dependent_binding_unpacked_at_use ctx id use_typ =
  match Bindings.find_opt id ctx.global.semantic_types.bindings with
  | Some typ ->
      has_top_level_dependent_type ctx typ
      && (not (has_top_level_dependent_type ctx use_typ))
      && not
           ( match ctx.expected_dependent with
           | Some expected -> dependent_types_equivalent ctx typ expected
           | None -> false
           )
  | None -> false

let dependent_representation_type ctx (E_aux (exp, _) as full_exp) =
  match exp with
  | E_id id when global_dependent_binding_unpacked_at_use ctx id (typ_of full_exp) -> typ_of full_exp
  | E_id id -> (
      match Bindings.find_opt id ctx.packed_dependent_types with
      | Some typ -> typ
      | None -> (
          match Bindings.find_opt id ctx.global.semantic_types.bindings with
          | Some typ when has_dependent_type ctx typ -> typ
          | _ -> typ_of full_exp
        )
    )
  | E_app (id, _) -> (
      match semantic_function_type ctx id with
      | Some (_, ret) ->
          let ret = subst_unifiers (instantiation_of full_exp) ret in
          if contains_prop_dependent_alias ctx ret then ret else typ_of full_exp
      | None -> typ_of full_exp
    )
  | _ -> typ_of full_exp

let rec exp_has_dependent_representation ctx (E_aux (exp, _) as full_exp) =
  let representation_typ = dependent_representation_type ctx full_exp in
  if not (has_dependent_type ctx representation_typ) then false
  else (
    match exp with
    | E_id id -> not (IdSet.mem id ctx.unpacked_dependent_ids)
    | E_typ (_, exp) -> exp_has_dependent_representation ctx exp
    | E_block [exp] -> exp_has_dependent_representation ctx exp
    | E_if (_, then_exp, else_exp) ->
        exp_has_dependent_representation ctx then_exp && exp_has_dependent_representation ctx else_exp
    | E_tuple exps -> (
        match expand_synonyms_for_dependent_type ctx representation_typ with
        | Typ_aux (Typ_tuple typs, _) when List.length typs = List.length exps ->
            List.for_all2
              (fun typ exp -> (not (has_dependent_type ctx typ)) || exp_has_dependent_representation ctx exp)
              typs exps
        | _ -> false
      )
    | E_struct _ | E_struct_update _ -> false
    | E_field (record_exp, field) -> (
        let field_typ =
          match typ_of record_exp with
          | Typ_aux (Typ_id record, _) | Typ_aux (Typ_app (record, _), _) ->
              Option.bind (Bindings.find_opt record ctx.global.semantic_types.record_fields) (Bindings.find_opt field)
          | _ -> None
        in
        match field_typ with
        | Some field_typ when prop_dependent_record_typ field_typ ->
            (* A proof-refined record field is stored as its raw carrier.
               Projection repacks it only when the enclosing record itself
               carries the validity proof from which the field proof follows. *)
            exp_has_dependent_representation ctx record_exp
        | Some field_typ ->
            (* Ordinary existential fields are stored in generated records as
               their nested Sigma representation, so projecting one already
               yields the represented value. *)
            has_dependent_type ctx field_typ
        | None -> false
      )
    | E_app _ -> true
    | _ -> true
  )

let rec doc_prop_dependent_result_carrier ctx carrier source_exp value =
  match prop_dependent_record_id_for_typ carrier with
  | Some record -> (
      let result_carrier = mk_id_typ record in
      match prop_dependent_result_of_exp ctx source_exp with
      | Some source_result when dependent_types_equivalent ctx source_result.result_carrier carrier ->
          parens value ^^ string ".val"
      | _ when exp_has_dependent_representation ctx source_exp -> (
          let source_typ = dependent_representation_type ctx source_exp in
          let expanded_source_typ = expand_synonyms_for_dependent_type ctx source_typ in
          match prop_dependent_record_application expanded_source_typ with
          | Some (source_record, _) when Id.compare source_record record = 0 ->
              parens (doc_id_ctor source_record ^^ string ".Indexed.toRefined " ^^ parens value)
          | _ -> (
              match prop_dependent_record_id_for_typ source_typ with
              | Some source_record when Id.compare source_record record = 0 ->
                  let base_validity =
                    match prop_dependent_record_application source_typ with
                    | Some _ -> parens value ^^ string ".property.1"
                    | None -> parens value ^^ string ".property"
                  in
                  string "⟨" ^^ parens value ^^ string ".val" ^^ comma_sp ^^ base_validity ^^ string "⟩"
              | _ -> doc_dependent_repack ctx source_typ result_carrier value
            )
        )
      | _ -> doc_dependent_pack ctx result_carrier value
    )
  | None ->
      let expanded = expand_synonyms_for_dependent_type ctx carrier in
      if Typ.compare expanded carrier <> 0 then doc_prop_dependent_result_carrier ctx expanded source_exp value
      else (
        match (expanded, source_exp) with
        | Typ_aux (Typ_tuple typs, _), E_aux (E_tuple exps, _) when List.length typs = List.length exps ->
            let already_refined =
              List.for_all2
                (fun typ exp ->
                  (not (has_dependent_type ctx typ))
                  || exp_has_dependent_representation ctx exp
                     && dependent_types_equivalent ctx (dependent_representation_type ctx exp) typ
                )
                typs exps
            in
            if already_refined then value
            else (
              let names = List.mapi (fun index _ -> Printf.sprintf "dependentResultValue%i" index) typs in
              let pattern = parens (separate comma_sp (List.map string names)) in
              let converted =
                parens
                  (separate comma_sp
                     (List.map2
                        (fun (typ, exp) name -> doc_prop_dependent_result_carrier ctx typ exp (string name))
                        (List.combine typs exps) names
                     )
                  )
              in
              parens (dependent_lambda pattern converted ^^ space ^^ parens value)
            )
        | carrier, _ -> (
            match prop_dependent_result_of_exp ctx source_exp with
            | Some source_result when dependent_types_equivalent ctx source_result.result_carrier carrier ->
                parens value ^^ string ".val"
            | _ -> doc_dependent_pack ctx carrier value
          )
      )

let doc_prop_dependent_result_pack ctx result source_exp value =
  let binder = string "dependentResult" in
  let carrier = doc_prop_dependent_result_carrier ctx result.result_carrier source_exp binder in
  let body =
    string "let resultCarrier := " ^^ carrier ^^ hardline ^^ string "⟨resultCarrier, "
    ^^ prop_dependent_result_proof ctx result ^^ string "⟩"
  in
  parens (string "let " ^^ binder ^^ string " := " ^^ parens value ^^ hardline ^^ body)

(* Follow only the result-producing tails of control flow.  A function needs
   explicit constraint proofs precisely when at least one such tail still
   produces the carrier rather than an already refined public value. *)
let rec dependent_tail_has_representation ctx (E_aux (exp, _) as full_exp) =
  match exp with
  | E_if (_, then_exp, else_exp) ->
      dependent_tail_has_representation ctx then_exp && dependent_tail_has_representation ctx else_exp
  | E_match (_, clauses) ->
      List.for_all
        (fun (Pat_aux (clause, _)) ->
          match clause with
          | Pat_exp (_, branch) | Pat_when (_, _, branch) -> dependent_tail_has_representation ctx branch
        )
        clauses
  | E_let (_, _, body) | E_internal_plet (_, _, body) -> dependent_tail_has_representation ctx body
  | E_block exps -> (
      match List.rev exps with [] -> false | last :: _ -> dependent_tail_has_representation ctx last
    )
  | E_typ (_, inner) -> dependent_tail_has_representation ctx inner
  | _ -> exp_has_dependent_representation ctx full_exp

let rec dependent_tail_carrier_kids ctx (E_aux (exp, _) as full_exp) =
  match exp with
  | E_if (_, then_exp, else_exp) ->
      KidSet.union (dependent_tail_carrier_kids ctx then_exp) (dependent_tail_carrier_kids ctx else_exp)
  | E_match (_, clauses) ->
      List.fold_left
        (fun kids (Pat_aux (clause, _)) ->
          let branch = match clause with Pat_exp (_, branch) | Pat_when (_, _, branch) -> branch in
          KidSet.union kids (dependent_tail_carrier_kids ctx branch)
        )
        KidSet.empty clauses
  | E_let (_, _, body) | E_internal_plet (_, _, body) -> dependent_tail_carrier_kids ctx body
  | E_block exps -> (
      match List.rev exps with [] -> KidSet.empty | last :: _ -> dependent_tail_carrier_kids ctx last
    )
  | E_typ (_, inner) -> dependent_tail_carrier_kids ctx inner
  | _ -> if exp_has_dependent_representation ctx full_exp then KidSet.empty else lean_nvars_of_typ (typ_of full_exp)

(* A refined value may also be constructed before the result-producing tail,
   for example in a let binding.  Such a construction needs the enclosing
   function's relevant quantified constraints even when the final expression
   already carries its own validity proof. *)
let dependent_record_construction_kids ctx exp =
  let collect recurse kids (E_aux (aux, _) as exp) =
    let kids, exp = recurse kids exp in
    let kids =
      match aux with
      | (E_struct _ | E_struct_update _) when prop_dependent_record_typ (typ_of exp) ->
          KidSet.union kids (lean_nvars_of_typ (typ_of exp))
      | _ -> kids
    in
    (kids, exp)
  in
  fst (foldin_exp collect KidSet.empty exp)

let constraint_relevant_to kids nc = not (KidSet.is_empty (KidSet.inter kids (tyvars_of_constraint nc)))

let close_constraint_kids quant seeds =
  let rec close kids =
    let expanded =
      List.fold_left
        (fun expanded (QI_aux (item, _)) ->
          match item with
          | QI_constraint nc when constraint_relevant_to kids nc -> KidSet.union expanded (tyvars_of_constraint nc)
          | _ -> expanded
        )
        kids quant
    in
    if KidSet.equal kids expanded then kids else close expanded
  in
  close seeds

let debug_dependent_representation =
  match Sys.getenv_opt "SAIL_LEAN_DEPENDENT_DEBUG" with Some ("1" | "true" | "yes") -> true | _ -> false

let log_dependent_representation expected exp represented representation_typ needs_repack =
  if debug_dependent_representation then
    Printf.eprintf "lean-dependent: expected=%s expression=%s type=%s representation=%s represented=%b repack=%b\n%!"
      (string_of_typ expected) (string_of_exp exp)
      (string_of_typ (typ_of exp))
      (string_of_typ representation_typ) represented needs_repack

let record_id_of_typ = function Typ_aux (Typ_id id, _) | Typ_aux (Typ_app (id, _), _) -> Some id | _ -> None

let semantic_record_field ctx record_id field =
  match Bindings.find_opt record_id ctx.global.semantic_types.record_fields with
  | Some fields -> Bindings.find_opt field fields
  | None -> None

let semantic_record_field_of_exp ctx exp field =
  match record_id_of_typ (typ_of exp) with Some id -> semantic_record_field ctx id field | None -> None

(* A record field whose Sail type is a singleton integer over the record's own
   index parameters carries no information the record type does not already
   fix.  Storing it would leave the index parameter phantom and make
   [value.field = index] -- the entire content of the singleton type --
   unrecoverable in Lean.  Such a field is therefore not stored at all: it is
   emitted as a projection returning the index, so the equation holds by [rfl].

   The guard on the rendered kinds keeps the projection well typed.  A field
   rendered as [Nat] must be built from index parameters that are themselves
   rendered as [Nat]; the reverse direction is covered by Lean's coercion. *)
let record_index_projection_nexp ctx id tq typ =
  if List.mem (string_of_id id) !opt_extern_types then
    (* The Lean declaration of an extern type is written by hand outside this
       backend, so its fields are whatever that declaration stores. *)
    None
  else (
    let env = try Env.add_typquant Unknown tq ctx.env with Type_internal.Type_error _ -> ctx.env in
    let field_ctx = context_init env ctx.global in
    let expanded = try Env.expand_synonyms env typ with Type_internal.Type_error _ -> typ in
    match expanded with
    | Typ_aux (Typ_app (Id_aux (Id ("atom" | "implicit"), _), [A_aux (A_nexp nexp, _)]), _) ->
        let quantified = KidSet.of_list (quantified_int_kids tq) in
        let vars = tyvars_of_nexp nexp in
        let renders_nat = provably_nneg field_ctx nexp in
        let var_renders_nat kid = provably_nneg field_ctx (Nexp_aux (Nexp_var kid, Unknown)) in
        if KidSet.subset vars quantified && ((not renders_nat) || KidSet.for_all var_renders_nat vars) then Some nexp
        else None
    | _ -> None
  )

let record_index_projection_field ctx record_id field =
  match
    (Bindings.find_opt record_id ctx.global.semantic_types.record_quants, semantic_record_field ctx record_id field)
  with
  | Some tq, Some typ -> record_index_projection_nexp ctx record_id tq typ
  | _ -> None

(* Whether the field of [record_id] is projected from an index rather than
   stored.  Every emitter that names a field -- structure declaration, literal
   construction, functional update, and pattern -- has to agree on this. *)
let record_field_is_projected ctx record_id field = Option.is_some (record_index_projection_field ctx record_id field)

let projected_fields_removed ctx record_id fexps =
  match record_id with
  | Some record_id ->
      List.filter (fun (FE_aux (FE_fexp (field, _), _)) -> not (record_field_is_projected ctx record_id field)) fexps
  | None -> fexps

(* Lean erases Sail singleton integer refinements to Nat/Int.  A projection
   whose inferred Sail type is atom(n) nevertheless has the unique value n;
   render that index directly so it remains definitionally equal to indices in
   the surrounding dependent record type. *)
let singleton_nexp_of_typ ctx typ =
  match Env.expand_synonyms ctx.env typ with
  | Typ_aux (Typ_app (Id_aux (Id ("atom" | "implicit"), _), [A_aux (A_nexp nexp, _)]), _) ->
      let available kid =
        KidSet.mem kid ctx.function_bound_nvars || KBindings.mem kid ctx.kid_docs
        || match KBindings.find_opt kid ctx.kid_id_renames with Some (Some _) -> true | _ -> false
      in
      if KidSet.for_all available (tyvars_of_nexp nexp) then Some nexp else None
  | _ -> None

let doc_raw_typ ctx env typ =
  let ctx = context_with_env ctx env in
  doc_typ ctx (Env.expand_synonyms env typ)

let captured_typ_var ((i, Typ_aux (t, _)) as typ) =
  match t with
  | Typ_app (Id_aux (Id "atom", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)])
  | Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]) ->
      Some (i, ki)
  | _ -> None

let doc_typ_id ctx ((fid, typ), _) = flow (break 1) [doc_id_ctor fid; colon; doc_typ ctx typ]

let doc_kind ctx (kid : kid) (K_aux (k, _)) =
  match k with
  | K_int -> if provably_nneg ctx (Nexp_aux (Nexp_var kid, Unknown)) then string "Nat" else string "Int"
  | K_bool -> string "Bool"
  | K_type -> string "Type"

let doc_quant_item_all ctx (QI_aux (qi, _)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_kind (k, ki), _)) -> flow (break 1) [doc_kid ctx ki; colon; doc_kind ctx ki k]
  | QI_constraint c -> doc_nconstraint ctx c

(* Used to annotate types with the original constraints *)
let doc_typ_quant_all ctx qs = List.map (doc_quant_item_all ctx) qs

let doc_typ_quant_in_comment ctx tq =
  let typ_quants = doc_typ_quant_all ctx tq in
  if List.length typ_quants > 0 then
    (* an ordinary comment: a doc comment here would clash with the
       definition's Sail doc comment (two docstrings is a parse error) *)
    string "/- Type quantifiers: " ^^ nest 2 (flow comma_sp typ_quants) ^^ string " -/" ^^ hardline
  else empty

let doc_quant_item_relevant ctx (QI_aux (qi, annot)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_kind (k, ki), _)) -> Some (flow (break 1) [doc_kid ctx ki; colon; doc_kind ctx ki k])
  | QI_constraint c -> None

(* Used to translate type parameters of types, so we drop the constraints *)
let doc_typ_quant_relevant ctx tq =
  (* We go through the type variables with an environment that contains all the constraints,
     in order to detect when we can translate the Kind as Nat *)
  let ctx = context_init (Type_check.Env.add_typquant Unknown tq ctx.env) ctx.global in
  List.filter_map (doc_quant_item_relevant ctx) tq

let doc_quant_item_only_vars ctx (QI_aux (qi, annot)) =
  match qi with QI_id (KOpt_aux (KOpt_kind (k, ki), _)) -> Some (doc_kid ctx ki) | QI_constraint c -> None

(* Used to translate type parameters of type abbreviations *)
let doc_typ_quant_only_vars ctx tq = List.filter_map (doc_quant_item_only_vars ctx) tq

let lean_escape_string s = Str.global_replace (Str.regexp "\"") "\\\"" s

let doc_lit ~width (L_aux (lit, l)) =
  match lit with
  | L_unit -> string "()"
  | L_false -> string "false"
  | L_true -> string "true"
  | L_num i -> doc_big_int i
  | L_hex [] | L_bin [] -> string "BitVec.nil"
  | L_hex hex ->
      let width_specifier = if width then "#" ^ string_of_int (hex_lit_length hex) else "" in
      utf8string ("0x" ^ string_of_hex_lit ~group_separator:"" ~case:Uppercase hex ^ width_specifier)
  | L_bin bin -> (
      let width_specifier = if width then "#" ^ string_of_int (bin_lit_length bin) else "" in
      (* Print single bits as just 0 or 1 without a 0b prefix *)
      match bin with
      | [Non_empty (Bin_0, [])] -> string ("0" ^ width_specifier)
      | [Non_empty (Bin_1, [])] -> string ("1" ^ width_specifier)
      | _ -> utf8string ("0b" ^ string_of_bin_lit ~group_separator:"" bin ^ width_specifier)
    )
  | L_string s -> utf8string ("\"" ^ lean_escape_string s ^ "\"")
  | L_real r -> utf8string (Q.to_string (Util.Rational.from_rocq r))
(* TODO test if this is really working *)

let string_of_exp_con (E_aux (e, _)) =
  match e with
  | E_block _ -> "E_block"
  | E_ref _ -> "E_ref"
  | E_if _ -> "E_if"
  | E_loop _ -> "E_loop"
  | E_for _ -> "E_for"
  | E_vector_append _ -> "E_vector_append"
  | E_list _ -> "E_list"
  | E_cons _ -> "E_cons"
  | E_struct _ -> "E_struct"
  | E_struct_update _ -> "E_struct_update"
  | E_field _ -> "E_field"
  | E_match _ -> "E_match"
  | E_assign _ -> "E_assign"
  | E_sizeof _ -> "E_sizeof"
  | E_constraint _ -> "E_constraint"
  | E_exit _ -> "E_exit"
  | E_throw _ -> "E_throw"
  | E_try _ -> "E_try"
  | E_return _ -> "E_return"
  | E_assert _ -> "E_assert"
  | E_var _ -> "E_var"
  | E_undef -> "E_undef"
  | E_internal_plet _ -> "E_internal_plet"
  | E_internal_return _ -> "E_internal_return"
  | E_internal_assume _ -> "E_internal_assume"
  | E_internal_value _ -> "E_internal_value"
  | E_id _ -> "E_id"
  | E_lit _ -> "E_lit"
  | E_typ _ -> "E_typ"
  | E_app _ -> "E_app"
  | E_tuple _ -> "E_tuple"
  | E_vector _ -> "E_vector"
  | E_let _ -> "E_let"
  | E_config _ -> "E_config"

let rec is_anonymous_pat (P_aux (p, _) as full_pat) =
  match p with
  | P_wild -> true
  | P_id (Id_aux (Id s, _)) -> String.sub s 0 1 = "_"
  | P_lit (L_aux _) -> true
  | P_typ (_, p) -> is_anonymous_pat p
  | _ -> false

let string_of_pat_con (P_aux (p, _)) =
  match p with
  | P_app _ -> "P_app"
  | P_wild -> "P_wild"
  | P_lit _ -> "P_lit"
  | P_or _ -> "P_or"
  | P_not _ -> "P_not"
  | P_as _ -> "P_as"
  | P_typ _ -> "P_typ"
  | P_id _ -> "P_id"
  | P_var _ -> "P_var"
  | P_vector _ -> "P_vector"
  | P_vector_concat _ -> "P_vector_concat"
  | P_vector_subrange _ -> "P_vector_subrange"
  | P_tuple _ -> "P_tuple"
  | P_list _ -> "P_list"
  | P_cons _ -> "P_cons"
  | P_string_append _ -> "P_string_append"
  | P_struct _ -> "P_struct"

let string_of_def (DEF_aux (d, _)) =
  match d with
  | DEF_type _ -> "DEF_type"
  | DEF_constraint _ -> "DEF_constraint"
  | DEF_fundef _ -> "DEF_fundef"
  | DEF_mapdef _ -> "DEF_mapdef"
  | DEF_impl _ -> "DEF_impl"
  | DEF_let _ -> "DEF_let"
  | DEF_val (VS_aux (VS_val_spec (_, id, _), _)) -> "DEF_val " ^ string_of_id id
  | DEF_outcome _ -> "DEF_outcome"
  | DEF_instantiation _ -> "DEF_instantiation"
  | DEF_fixity _ -> "DEF_fixity"
  | DEF_overload _ -> "DEF_overload"
  | DEF_default _ -> "DEF_default"
  | DEF_scattered _ -> "DEF_scattered"
  | DEF_measure _ -> "DEF_measure"
  | DEF_loop_measures _ -> "DEF_loop_measures"
  | DEF_register _ -> "DEF_register"
  | DEF_internal_mutrec _ -> "DEF_internal_mutrec"
  | DEF_pragma _ -> "DEF_pragma"

(** Fix identifiers to match the standard Lean library. *)
let fixup_match_id (Id_aux (id, l) as id') =
  match id with
  | Id id ->
      Id_aux (Id (match id with "Some" -> "some" | "None" -> "none" | "early_return" -> "throw" | _ -> fix_id id), l)
  | _ -> id'

let rec update_ctx_pat (ctx : context) (P_aux (p, (l, annot)) as pat) =
  match p with
  | P_var (P_aux (P_id id, _), TP_aux (TP_var kid, tp_l)) -> add_single_kid_id_rename ctx id kid
  | P_typ (_, p') | P_as (p', _) | P_var (p', _) -> update_ctx_pat ctx p'
  | P_app (_, pats) | P_vector pats | P_vector_concat pats | P_tuple pats | P_list pats | P_string_append pats ->
      List.fold_left update_ctx_pat ctx pats
  | _ -> ctx

let rec doc_pat ?(need_parens = false) ?(in_vector = false) ctx in_match_bv (P_aux (p, (l, annot)) as pat) =
  let opt_parens doc = if need_parens then parens doc else doc in
  let env = env_of_tannot annot in
  match p with
  | P_wild -> underscore
  | P_lit lit -> doc_lit ~width:false lit
  | P_typ (Typ_aux (Typ_id (Id_aux (Id "bit", _)), _), p) when in_vector -> doc_pat ctx in_match_bv p ^^ string ":1"
  | P_typ (Typ_aux (Typ_app (Id_aux (Id id, _), [A_aux (A_nexp (Nexp_aux (Nexp_constant i, _)), _)]), _), p)
    when in_vector && (id = "bits" || id = "bitvector") ->
      doc_pat ctx in_match_bv p ^^ string ":" ^^ doc_big_int i
  | P_typ (ptyp, p) when in_vector -> doc_pat ctx in_match_bv p ^^ string ":" ^^ doc_typ ctx ptyp
  | P_typ (ptyp, p) -> doc_pat ctx in_match_bv p
  | P_id id -> (
      match typ_of_pat pat with
      | Typ_aux (Typ_app (Id_aux (Id id', _), [A_aux (A_nexp (Nexp_aux (Nexp_constant i, _)), _)]), _)
        when in_vector && (id' = "bits" || id' = "bitvector") ->
          (fixup_match_id id |> doc_id_ctor) ^^ string ":" ^^ doc_big_int i
      | _ ->
          let prefix = if Type_check.is_enum_member id ctx.env then string "." else empty in
          prefix ^^ (fixup_match_id id |> doc_id_ctor)
    )
  | P_tuple pats -> separate (string ", ") (List.map (doc_pat ctx in_match_bv) pats) |> parens
  | P_list pats -> separate (string ", ") (List.map (doc_pat ctx in_match_bv) pats) |> brackets
  | P_vector pats
    when List.for_all (fun p -> match p with P_aux (P_lit _, _) -> true | _ -> false) pats && not in_match_bv ->
      string "0b" ^^ concat (List.map (doc_pat ~in_vector:true ctx in_match_bv) pats)
  | P_vector pats -> concat (List.map (doc_pat ~in_vector:true ctx in_match_bv) pats)
  | P_vector_concat pats -> doc_vector_concat pats
  | P_app (Id_aux (Id "None", _), p) -> string "none"
  | P_app (cons, pats) ->
      let constructor_arg_typs =
        match semantic_function_type ctx cons with
        | Some (arg_typs, _) -> arg_typs
        | None -> (
            try
              let _, typ = Env.get_val_spec cons ctx.env in
              match typ with Typ_aux (Typ_fn (arg_typs, _), _) -> arg_typs | _ -> []
            with _ -> []
          )
      in
      let doc_constructor_pat index typ pat =
        let pattern = doc_pat ~need_parens:true ctx in_match_bv pat in
        let proof = string (Printf.sprintf "_sailValidity%i" index) in
        doc_dependent_pattern ~proof ctx typ pattern
      in
      let constructor_pats =
        try
          List.mapi (fun index (typ, pat) -> doc_constructor_pat index typ pat) (List.combine constructor_arg_typs pats)
        with Invalid_argument _ -> List.mapi (fun index pat -> doc_constructor_pat index (typ_of_pat pat) pat) pats
      in
      opt_parens (string "." ^^ doc_id_ctor (fixup_match_id cons) ^^ space ^^ separate (string ", ") constructor_pats)
  | P_var (p, _) -> doc_pat ctx in_match_bv p
  | P_as (pat, id) -> doc_pat ctx in_match_bv pat
  | P_struct (struct_name, pats, _) ->
      (* A field projected from an index is not stored, so it cannot appear in
         a structure pattern.  Nothing is lost as long as the sub-pattern binds
         no names; a binder would have to be recovered from the index instead,
         which a pattern cannot express. *)
      let record_id = match struct_name with SN_id id -> Some id | SN_anon -> record_id_of_typ (typ_of_pat pat) in
      let projected field =
        match record_id with Some record_id -> record_field_is_projected ctx record_id field | None -> false
      in
      let pats =
        List.filter
          (fun (field, sub) ->
            if not (projected field) then true
            else if IdSet.is_empty (pat_ids sub) then false
            else
              failwith
                ("Lean backend cannot bind " ^ string_of_id field
               ^ " in a structure pattern: the field is projected from a type index"
                )
          )
          pats
      in
      let pats =
        List.map (fun (id, pat) -> separate space [doc_id_ctor id; coloneq; doc_pat ctx in_match_bv pat]) pats
      in
      braces (space ^^ separate (comma ^^ space) pats ^^ space)
  | P_cons (hd_pat, tl_pat) ->
      parens (separate space [doc_pat ctx in_match_bv hd_pat; string "::"; doc_pat ctx in_match_bv tl_pat])
  | _ -> failwith ("Doc Pattern " ^ string_of_pat_con pat ^ " " ^ string_of_pat pat ^ " not translatable yet.")

and doc_vector_concat pats =
  let rec doc_part (P_aux (aux, (l, _)) as pat) =
    match aux with
    | P_lit (L_aux (L_bin bin, _)) ->
        let bits = BitList.of_bin_lit bin in
        concat_map (function B0 -> char '0' | B1 -> char '1') bits
    | P_lit (L_aux (L_hex hex, _)) ->
        let bits = BitList.of_hex_lit hex in
        concat_map (function B0 -> char '0' | B1 -> char '1') bits
    | P_id id -> (
        match destruct_bitvector (env_of_pat pat) (typ_of_pat pat) with
        | Some (Nexp_aux (Nexp_constant n, _)) ->
            doc_id_ctor (fixup_match_id id) ^^ char ':' ^^ string (Big_int.to_string n)
        | _ -> Reporting.unreachable l __POS__ "Found subpattern with unclear width in bitvector pattern"
      )
    | P_typ (_, pat) -> doc_part pat
    | P_vector pats -> separate_map comma doc_part pats
    | _ -> Reporting.unreachable l __POS__ ("Unexpected pattern in match_bv vector_concat pattern " ^ string_of_pat pat)
  in
  brackets (separate_map comma doc_part pats)

let rec pattern_destructures_value (P_aux (pat, _)) =
  match pat with
  | P_typ (_, pat) | P_var (pat, _) -> pattern_destructures_value pat
  | P_tuple _ | P_list _ | P_vector _ | P_vector_concat _ | P_string_append _ | P_cons _ | P_app _ | P_struct _ -> true
  | P_lit _ | P_wild | P_or _ | P_not _ | P_as _ | P_id _ | P_vector_subrange _ -> false

let rec nested_dependent_pattern_bindings ctx typ (P_aux (pat, _)) =
  let recurse = nested_dependent_pattern_bindings ctx in
  let recurse_many typs pats =
    try
      List.fold_left2
        (fun bindings typ pat -> Bindings.fold Bindings.add (recurse typ pat) bindings)
        Bindings.empty typs pats
    with Invalid_argument _ -> Bindings.empty
  in
  match pat with
  | P_typ (annotated, pat) -> recurse annotated pat
  | P_var (pat, _) -> recurse typ pat
  | P_as (pat, id) ->
      let bindings = recurse typ pat in
      if has_top_level_dependent_type ctx typ then Bindings.add id typ bindings else bindings
  | P_id id -> if has_top_level_dependent_type ctx typ then Bindings.singleton id typ else Bindings.empty
  | P_tuple pats -> (
      match expand_synonyms_for_dependent_type ctx typ with
      | Typ_aux (Typ_tuple typs, _) -> recurse_many typs pats
      | _ -> Bindings.empty
    )
  | P_app (constructor, pats) ->
      let arg_typs =
        match semantic_function_type ctx constructor with
        | Some (arg_typs, _) -> arg_typs
        | None -> (
            try
              let _, typ = Env.get_val_spec constructor ctx.env in
              match typ with Typ_aux (Typ_fn (arg_typs, _), _) -> arg_typs | _ -> []
            with _ -> []
          )
      in
      recurse_many arg_typs pats
  | _ -> Bindings.empty

let doc_pat_for_type ctx in_match_bv typ pat =
  let typ = expand_synonyms_for_dependent_type ctx typ in
  match typ with
  | Typ_aux (Typ_exist (kopts, _, inner), _) when pattern_destructures_value pat ->
      List.fold_right
        (fun (KOpt_aux (KOpt_kind (_, kid), _)) pattern ->
          string "⟨" ^^ doc_kid ctx kid ^^ string ", " ^^ pattern ^^ string "⟩"
        )
        (relevant_existential_kopts kopts inner)
        (doc_pat ctx in_match_bv pat)
  | _ -> doc_pat ctx in_match_bv pat

let rec first_pattern_binder (P_aux (pat, _)) =
  let first pats = List.find_map first_pattern_binder pats in
  match pat with
  | P_id id -> Some id
  | P_typ (_, pat) | P_var (pat, _) | P_as (pat, _) -> first_pattern_binder pat
  | P_tuple pats | P_list pats | P_vector pats | P_vector_concat pats -> first pats
  | P_app (_, pats) | P_string_append pats -> first pats
  | P_cons (head, tail) -> (
      match first_pattern_binder head with Some _ as binder -> binder | None -> first_pattern_binder tail
    )
  | P_struct (_, fields, _) -> List.find_map (fun (_, pat) -> first_pattern_binder pat) fields
  | P_lit _ | P_wild | P_or _ | P_not _ | P_vector_subrange _ -> None

let existential_pattern_kid_docs ctx typ pat =
  let typ = expand_synonyms_for_dependent_type ctx typ in
  match (typ, first_pattern_binder pat) with
  | Typ_aux (Typ_exist (kopts, _, inner), _), Some binder when pattern_destructures_value pat ->
      List.fold_left
        (fun docs (KOpt_aux (KOpt_kind (_, kid), _)) ->
          let (Kid_aux (Var raw_name, _)) = kid in
          let kind_name = String.sub raw_name 1 (String.length raw_name - 1) in
          let witness = fix_id (string_of_id binder ^ "_" ^ kind_name) in
          KBindings.add kid (string witness) docs
        )
        KBindings.empty
        (relevant_existential_kopts kopts inner)
  | _ -> KBindings.empty

let context_with_pattern_kid_docs ctx docs = { ctx with kid_docs = KBindings.fold KBindings.add docs ctx.kid_docs }

(* Relate the fresh index variables in a typed expression or pattern back to
   the witnesses carried by its public nested-Sigma type.  Ordinary Lean
   extraction erases Sail constraints, but it must retain these equalities in
   the generated names/paths so later dependent type annotations remain
   well-scoped. *)
let add_existential_carrier_witness_docs ctx public_typ candidate_typs witness_doc =
  let rec existential_carrier ctx kopts typ =
    let typ = expand_synonyms_for_dependent_type ctx typ in
    match typ with
    | Typ_aux (Typ_exist (outer_kopts, nc, inner), l) ->
        let env = List.fold_left (fun env kopt -> Env.add_typ_var l kopt env) ctx.env outer_kopts in
        let env = try Env.add_constraint nc env with Type_internal.Type_error _ -> env in
        existential_carrier (context_with_env ctx env) (kopts @ relevant_existential_kopts outer_kopts inner) inner
    | _ -> (ctx, kopts, typ)
  in
  let carrier_ctx, witness_kopts, carrier_typ = existential_carrier ctx [] public_typ in
  let add_candidate ctx candidate_typ =
    try
      let goals = KidSet.of_list (List.map kopt_kid witness_kopts) in
      let unifiers = Type_check.unify (typ_loc candidate_typ) carrier_ctx.env goals carrier_typ candidate_typ in
      List.mapi (fun index kopt -> (index, kopt_kid kopt)) witness_kopts
      |> List.fold_left
           (fun ctx (index, witness) ->
             match KBindings.find_opt witness unifiers with
             | Some (A_aux (A_nexp (Nexp_aux (Nexp_var raw_kid, _)), _)) ->
                 { ctx with kid_docs = KBindings.add raw_kid (witness_doc index witness) ctx.kid_docs }
             | _ -> ctx
           )
           ctx
    with _ -> ctx
  in
  List.fold_left add_candidate ctx candidate_typs

let semantic_unpack_binding ctx id typ =
  if has_semantic_range ctx typ then
    [string "let " ^^ doc_id_ctor id ^^ string " := " ^^ doc_semantic_unpack ctx typ (doc_id_ctor id)]
  else []

let rec semantic_pattern_unpacks_with_typ ctx typ (P_aux (pat, _)) =
  let recurse typ pat = semantic_pattern_unpacks_with_typ ctx (Some typ) pat in
  let recurse_many typs pats = try List.concat (List.map2 recurse typs pats) with Invalid_argument _ -> [] in
  match pat with
  | P_id id -> Option.fold ~none:[] ~some:(semantic_unpack_binding ctx id) typ
  | P_typ (annotated, pat) -> recurse (Option.value ~default:annotated typ) pat
  | P_var (pat, _) -> semantic_pattern_unpacks_with_typ ctx typ pat
  | P_as (pat, id) ->
      let nested = semantic_pattern_unpacks_with_typ ctx typ pat in
      let binding = Option.fold ~none:[] ~some:(semantic_unpack_binding ctx id) typ in
      nested @ binding
  | P_tuple pats -> (
      match typ with Some (Typ_aux (Typ_tuple typs, _)) -> recurse_many typs pats | _ -> []
    )
  | P_list pats -> (
      match typ with
      | Some (Typ_aux (Typ_app (Id_aux (Id "list", _), [A_aux (A_typ inner, _)]), _)) ->
          List.concat_map (recurse inner) pats
      | _ -> []
    )
  | P_cons (head, tail) -> (
      match typ with
      | Some (Typ_aux (Typ_app (Id_aux (Id "list", _), [A_aux (A_typ inner, _)]), _) as list_typ) ->
          recurse inner head @ recurse list_typ tail
      | _ -> []
    )
  | P_app (constructor, pats) -> (
      match semantic_function_type ctx constructor with
      | Some (arg_typs, _) -> recurse_many arg_typs pats
      | None -> (
          match (typ, pats) with
          | Some (Typ_aux (Typ_app (Id_aux (Id "option", _), [A_aux (A_typ inner, _)]), _)), [pat] -> recurse inner pat
          | _ -> []
        )
    )
  | _ -> []

let semantic_pattern_unpacks ctx pat = semantic_pattern_unpacks_with_typ ctx None pat

(* Constructor patterns unwrap Prop-backed payload refinements so the Sail
   pattern continues to bind the carrier.  Track those carrier bindings
   explicitly: subsequent expressions must repack them for a refined target,
   and the named validity field emitted by [doc_dependent_pattern] supplies
   the proof. *)
let rec dependent_pattern_unpacked_ids ctx typ (P_aux (pat, _)) =
  let recurse typ pat = dependent_pattern_unpacked_ids ctx typ pat in
  let recurse_many typs pats =
    try List.fold_left2 (fun ids typ pat -> IdSet.union ids (recurse typ pat)) IdSet.empty typs pats
    with Invalid_argument _ -> IdSet.empty
  in
  match pat with
  | P_typ (annotated, pat) -> recurse annotated pat
  | P_var (pat, _) | P_as (pat, _) -> recurse typ pat
  | P_app (constructor, pats) -> (
      match semantic_function_type ctx constructor with
      | Some (arg_typs, _) -> (
          try
            List.fold_left2
              (fun ids arg_typ pat ->
                let ids = if has_top_level_dependent_type ctx arg_typ then IdSet.union ids (pat_ids pat) else ids in
                IdSet.union ids (recurse arg_typ pat)
              )
              IdSet.empty arg_typs pats
          with Invalid_argument _ -> IdSet.empty
        )
      | None -> IdSet.empty
    )
  | P_tuple pats -> (
      match expand_synonyms_for_dependent_type ctx typ with
      | Typ_aux (Typ_tuple typs, _) -> recurse_many typs pats
      | _ -> IdSet.empty
    )
  | P_list pats -> (
      match expand_synonyms_for_dependent_type ctx typ with
      | Typ_aux (Typ_app (Id_aux (Id "list", _), [A_aux (A_typ inner, _)]), _) ->
          List.fold_left (fun ids pat -> IdSet.union ids (recurse inner pat)) IdSet.empty pats
      | _ -> IdSet.empty
    )
  | P_cons (head, tail) -> (
      match expand_synonyms_for_dependent_type ctx typ with
      | Typ_aux (Typ_app (Id_aux (Id "list", _), [A_aux (A_typ inner, _)]), _) as list_typ ->
          IdSet.union (recurse inner head) (recurse list_typ tail)
      | _ -> IdSet.empty
    )
  | _ -> IdSet.empty

let context_with_dependent_pattern_unpacks ctx pat =
  let unpacked = dependent_pattern_unpacked_ids ctx (typ_of_pat pat) pat in
  let packed = nested_dependent_pattern_bindings ctx (typ_of_pat pat) pat in
  let packed = IdSet.fold (fun id bindings -> Bindings.remove id bindings) unpacked packed in
  let ctx =
    {
      ctx with
      unpacked_dependent_ids = IdSet.union ctx.unpacked_dependent_ids unpacked;
      packed_dependent_types =
        IdSet.fold (fun id bindings -> Bindings.remove id bindings) unpacked ctx.packed_dependent_types;
    }
  in
  Bindings.fold
    (fun id typ ctx ->
      {
        ctx with
        unpacked_dependent_ids = IdSet.remove id ctx.unpacked_dependent_ids;
        packed_dependent_types = Bindings.add id typ ctx.packed_dependent_types;
      }
    )
    packed ctx

let doc_pat_typ_ascription ctx (P_aux (p, (l, annot)) as pat) =
  match p with
  | P_typ (ptyp, _) ->
      Some
        ( if contains_prop_dependent_alias ctx ptyp then doc_dependent_shape ctx ptyp
          else doc_raw_typ ctx (env_of_pat pat) ptyp
        )
  | _ -> None

(* Copied from the Coq PP *)
let rebind_cast_pattern_vars pat typ exp =
  let rec aux pat typ =
    match (pat, typ) with
    | P_aux (P_typ (target_typ, P_aux (P_id id, (l, ann))), _), source_typ when not (is_enum (env_of exp) id) ->
        if Typ.compare target_typ source_typ == 0 then []
        else (
          let l = Parse_ast.Generated l in
          let cast_annot = Type_check.replace_typ source_typ ann in
          let e_annot = Type_check.mk_tannot (env_of exp) source_typ in
          [(pat, E_aux (E_id id, (l, e_annot)))]
        )
    | P_aux (P_tuple pats, _), Typ_aux (Typ_tuple typs, _) -> List.concat (List.map2 aux pats typs)
    | _ -> []
  in
  let add_lb (E_aux (_, ann) as exp) (pat, bind) = E_aux (E_let (pat, bind, exp), ann) in
  (* Don't introduce new bindings at the top-level, we'd just go into a loop. *)
  let lbs =
    match (pat, typ) with
    | P_aux (P_tuple pats, _), Typ_aux (Typ_tuple typs, _) -> List.concat (List.map2 aux pats typs)
    | _ -> []
  in
  List.fold_left add_lb exp lbs

let wrap_with_pure (needs_return : bool) ?(with_parens = false) (d : document) =
  if needs_return then (
    let d = if with_parens then parens d else d in
    parens (nest 2 (flow space [string "pure"; d]))
  )
  else d

let wrap_with_left_arrow (needs_left_arrow : bool) (d : document) =
  if needs_left_arrow then parens (nest 2 (flow space [leftarrow; d])) else d

let wrap_with_do (with_arrow : bool) (needs_return : bool) (d : document) =
  let ar_do = if with_arrow then string "← do" else string "do" in
  if needs_return then parens (nest 2 (flow hardline [ar_do; d])) else d

let get_fn_implicits (Typ_aux (t, _)) : bool list =
  let arg_implicit arg =
    match arg with
    | Typ_aux (Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]), _) -> true
    | _ -> false
  in
  match t with Typ_fn (args, cod) -> List.map arg_implicit args | _ -> []

let rec is_bitvector_pattern (P_aux (pat, _)) =
  match pat with P_vector _ | P_vector_concat _ -> true | P_as (pat, _) -> is_bitvector_pattern pat | _ -> false

let is_match_bv =
  List.exists (function Pat_aux (Pat_exp (pat, _), _) | Pat_aux (Pat_when (pat, _, _), _) -> is_bitvector_pattern pat)

let rec doc_implicit_args ?(docs = []) ns ims d_args =
  match (ns, ims, d_args) with
  | [], [], [] -> docs
  | n :: ns, im :: ims, d_arg :: d_args ->
      (* It would be nice to be able to know if the argument was in the source code. *)
      let docs = if im then parens (string n ^^ space ^^ coloneq ^^ space ^^ d_arg) :: docs else docs in
      doc_implicit_args ~docs ns ims d_args
  | _, _, _ -> []

(* Sail's singleton integer arguments are erased to Nat/Int in Lean.  When a
   quantified numeric variable also occurs in another, genuinely indexed
   argument type, Lean can therefore lose the equation that would normally
   infer its auto-implicit.  Preserve the typechecker's instantiation
   explicitly for precisely the variables that survive in the rendered
   function type. *)
let doc_instantiated_nvars ctx quantified f_typ instantiation =
  let visible, inferable =
    match f_typ with
    | Typ_aux (Typ_fn (args, ret), _) ->
        let visible, captured, inferable =
          List.fold_left
            (fun (visible, captured, inferable) typ ->
              let visible = KidSet.union visible (KidSet.diff (lean_nvars_of_typ typ) captured) in
              let inferable = KidSet.union inferable (lean_nvars_of_typ (expand_synonyms_for_dependent_type ctx typ)) in
              let captured =
                match captured_typ_var (mk_id "_", typ) with
                | Some (_, kid) -> KidSet.add kid captured
                | None -> captured
              in
              (visible, captured, inferable)
            )
            (KidSet.empty, KidSet.empty, KidSet.empty)
            args
        in
        (KidSet.union visible (KidSet.diff (lean_nvars_of_typ ret) captured), inferable)
    | _ -> (KidSet.empty, KidSet.empty)
  in
  let declared = KidSet.of_list (List.map kopt_kid (quant_kopts quantified)) in
  KBindings.bindings instantiation
  |> List.filter_map (fun (kid, arg) ->
      match arg with
      | A_aux (A_nexp nexp, _)
        when KidSet.mem kid declared && KidSet.mem kid visible
             && (not (KidSet.mem kid inferable))
             && KidSet.for_all (dependent_type_nvar_available ctx) (tyvars_of_nexp nexp) ->
          Some (parens (doc_kid ctx kid ^^ space ^^ coloneq ^^ space ^^ doc_typ_arg ctx `All arg))
      | _ -> None
  )

let op_of_id id =
  match id with
  | Some "_lean_and" -> `Binop "&&"
  | Some "_lean_or" -> `Binop "||"
  | Some "_lean_beq" -> `Binop "=="
  | Some "_lean_bne" -> `Binop "!="
  | Some "_lean_not" -> `Unop "!"
  | Some "_lean_add" -> `Binop "+"
  | Some "_lean_addi" -> `Binop "+i"
  | Some "_lean_sub" -> `Binop "-"
  | Some "_lean_subi" -> `Binop "-i"
  | Some "_lean_mul" -> `Binop "*"
  | Some "_lean_muli" -> `Binop "*i"
  | Some "_lean_div" -> `Binop "/"
  | Some "_lean_app" -> `Binop "+++" (* see issue sail#1630 *)
  | Some "_lean_bvand" -> `Binop "&&&"
  | Some "_lean_bvor" -> `Binop "|||"
  | Some "_lean_bvxor" -> `Binop "^^^"
  | Some "_lean_shiftl" -> `Binop "<<<"
  | Some "_lean_shiftr" -> `Binop ">>>"
  | Some "_lean_lt" -> `Binop "<b"
  | Some "_lean_ge" -> `Binop "≥b"
  | Some "_lean_le" -> `Binop "≤b"
  | Some "_lean_gt" -> `Binop ">b"
  | Some "_lean_pow2" -> `Unop "2 ^"
  | Some "_lean_pow2i" -> `Unop "2 ^i"
  | _ -> `NotOp

let typ_is_lean_nat env typ =
  match Env.expand_synonyms env typ with
  | Typ_aux (Typ_id (Id_aux (Id "nat", _)), _) -> true
  | typ -> (
      match Type_check.destruct_range env typ with
      | Some (_, constraint_, low, _) -> Type_check.prove __POS__ env (nc_or (nc_not constraint_) (nc_gteq low (nint 0)))
      | None -> false
    )

let unnop_of_id id = match id with Some "_lean_pow2" -> Some "2 ^ " | _ -> None

let is_loop id =
  match string_of_id id with "while#" | "while#t" | "foreach#" | "until#" | "until#t" -> true | _ -> false

let has_loop (e : 'a exp) =
  let e_app (id, args) = is_loop id || List.fold_left ( || ) false args in
  let e_return _ = true in
  fold_exp { (pure_exp_alg false ( || )) with e_app; e_return } e

let is_effect_id id = match string_of_id id with "while#" | "foreach#" | "early_return" -> true | _ -> false

let has_effect_app e =
  let e_app (id, args) = is_effect_id id || List.fold_left ( || ) false args in
  let e_return _ = true in
  fold_exp { (pure_exp_alg false ( || )) with e_app; e_return } e

let has_effect e = effectful (effect_of e) || has_effect_app e

let doc_loop_var (E_aux (e, (l, _)) as exp) =
  match e with
  | E_id id ->
      let id_pp = doc_id_ctor id in
      let typ = typ_of exp in
      (id_pp, id_pp)
  | E_lit (L_aux (L_unit, _)) -> (string "()", underscore)
  | _ -> raise (Reporting.err_unreachable l __POS__ ("Bad expression for variable in loop: " ^ string_of_exp exp))

let make_loop_vars extra_binders varstuple =
  match varstuple with
  | E_aux (E_tuple vs, _) ->
      let vs = List.map doc_loop_var vs in
      let mkpp f vs = separate (string ", ") (List.map f vs) in
      let tup_pp = mkpp (fun (pp, _) -> pp) vs in
      let match_pp = mkpp (fun (_, pp) -> pp) vs in
      (parens tup_pp, separate space ((string "λ" :: extra_binders) @ [parens match_pp; string "=>"]))
  | _ ->
      let exp_pp, match_pp = doc_loop_var varstuple in
      (exp_pp, separate space ((string "λ" :: extra_binders) @ [match_pp; string "=>"]))

let name_loop_vars ctx =
  let ll = ctx.loop_level in
  ctx.loop_level <- ll + 1;
  match ll with 0 -> (string "loop_vars", ctx) | _ -> (string "loop_vars_" ^^ string (string_of_int ll), ctx)

let name_if_hypothesis ctx =
  let level = ctx.if_level in
  ctx.if_level <- level + 1;
  string ("_sailIf" ^ string_of_int level)

let prepend_monad ctx exp doc =
  match (ctx.in_sail_monad, ctx.in_except_monad) with
  | true, Some ty -> [string "SailME"; ty; doc]
  | true, None -> [string "SailM"; doc]
  | false, Some ty -> [string "ExceptM"; ty; doc]
  | false, None -> [string "Id"; doc]

let match_or_match_bv (is_match_bv : bool) brs = if is_match_bv then "match_bv " else "match "

(* Push an expected dependent result type into the tails of control flow.
   Different branches may choose different existential witnesses, so they
   must construct their Sigma values before Lean attempts to unify the branch
   result types. *)
let rec annotate_dependent_tail public_typ (E_aux (exp, annot) as full_exp) =
  let recurse = annotate_dependent_tail public_typ in
  match exp with
  | E_if (condition, then_exp, else_exp) -> E_aux (E_if (condition, recurse then_exp, recurse else_exp), annot)
  | E_match (discriminant, clauses) ->
      let rewrite_clause (Pat_aux (clause, clause_annot)) =
        match clause with
        | Pat_exp (pat, branch) -> Pat_aux (Pat_exp (pat, recurse branch), clause_annot)
        | Pat_when (pat, guard, branch) -> Pat_aux (Pat_when (pat, guard, recurse branch), clause_annot)
      in
      E_aux (E_match (discriminant, List.map rewrite_clause clauses), annot)
  | E_let (pat, bind, body) -> E_aux (E_let (pat, bind, recurse body), annot)
  | E_internal_plet (pat, bind, body) -> E_aux (E_internal_plet (pat, bind, recurse body), annot)
  | E_block exps -> (
      match List.rev exps with
      | [] -> E_aux (E_typ (public_typ, full_exp), annot)
      | last :: rest -> E_aux (E_block (List.rev (recurse last :: rest)), annot)
    )
  | E_typ (_, inner) -> recurse inner
  | _ -> E_aux (E_typ (public_typ, full_exp), annot)

let rec doc_match_clause (is_bv : bool) (as_monadic : bool) ctx (Pat_aux (cl, l) as p) =
  match cl with
  | Pat_exp (pat, branch) ->
      let branch_ctx = context_with_dependent_pattern_unpacks ctx pat in
      let branch = separate hardline (semantic_pattern_unpacks ctx pat @ [wrap_exp as_monadic branch_ctx branch]) in
      group
        (nest 2
           (string "| " ^^ doc_pat ctx is_bv pat ^^ string " =>"
           ^^ string (if is_bv && as_monadic then " do" else "")
           ^^ break 1 ^^ branch
           )
        )
  | Pat_when (pat, when_, branch) when is_bv ->
      let branch_ctx = context_with_dependent_pattern_unpacks ctx pat in
      group
        (nest 2
           (string "| " ^^ doc_pat ctx is_bv pat ^^ string " if " ^^ doc_exp false branch_ctx when_ ^^ string " =>"
           ^^ string (if is_bv && as_monadic then " do" else "")
           ^^ break 1 ^^ wrap_exp as_monadic branch_ctx branch
           )
        )
  | Pat_when (pat, when_, branch) ->
      failwith ("The Lean backend does not support 'when' clauses in patterns:\n" ^ string_of_pexp p)

and wrap_exp as_monadic ctx e =
  let with_arrow = not as_monadic in
  let d = doc_exp as_monadic ctx e in
  match e with
  | E_aux (arg', _) -> (
      match arg' with
      | E_typ (_, e) when has_effect e -> wrap_with_do with_arrow true d
      | E_typ (_, e) when has_early_return e -> parens d
      | E_let _ | E_internal_plet _ | E_if _ | E_match _ | E_var _ | E_block _ ->
          if has_effect e then wrap_with_do with_arrow true d else parens d
      | _ when has_loop e -> wrap_with_do with_arrow true d
      | _ -> d
    )

(* TODO: refactor this function *)
and doc_loop l as_monadic ctx loop_kind args =
  let lambda effects lambda_pp d =
    let lambda_pp = if effects then lambda_pp ^^ string " do" else lambda_pp in
    parens (prefix 2 1 (group lambda_pp) d)
  in
  let cond, varstuple, body, measure =
    match args with
    | [cond; varstuple; body] -> (cond, varstuple, body, None)
    | [cond; varstuple; body; measure] -> (cond, varstuple, body, Some measure)
    | _ -> raise (Reporting.err_unreachable l __POS__ "Unexpected number of arguments for loop combinator")
  in
  let body =
    match body with
    | E_aux
        ( E_internal_plet
            ( P_aux ((P_wild | P_typ (_, P_aux (P_wild, _))), _),
              E_aux
                ( E_assert
                    (E_aux (E_lit (L_aux (L_true, _)), _), E_aux (E_lit (L_aux (L_string "loop dummy assert", _)), _)),
                  _
                ),
              body'
            ),
          _
        ) ->
        body'
    | _ -> body
  in
  let body_effects = has_effect body in
  let (E_aux (_, annot)) = cond in
  let cond_effects = has_effect cond in
  let vartuple_pp, base_lambda = make_loop_vars [] varstuple in
  let loop_ctx =
    let variables = match varstuple with E_aux (E_tuple variables, _) -> variables | variable -> [variable] in
    List.fold_left
      (fun ctx (E_aux (expression, _) as variable) ->
        match expression with
        | E_id id ->
            let public_typ = dependent_representation_type ctx variable in
            if has_top_level_dependent_type ctx public_typ then (
              let ctx =
                {
                  ctx with
                  unpacked_dependent_ids = IdSet.remove id ctx.unpacked_dependent_ids;
                  packed_dependent_types = Bindings.add id public_typ ctx.packed_dependent_types;
                }
              in
              let rec witness_path value index =
                if index = 0 then parens value ^^ string ".1" else witness_path (parens value ^^ string ".2") (index - 1)
              in
              add_existential_carrier_witness_docs ctx public_typ
                [typ_of variable]
                (fun index _ -> witness_path (doc_id_ctor id) index)
            )
            else ctx
        | _ -> ctx
      )
      ctx variables
  in
  let vars_pp, body_ctx = name_loop_vars loop_ctx in
  let body_pp = doc_exp body_effects body_ctx body in
  let vars_dec_pp = string "let mut " ^^ vars_pp ^^ string " := " ^^ vartuple_pp in
  let cond_pp = doc_exp cond_effects loop_ctx cond in
  let cond_pp = lambda cond_effects base_lambda cond_pp in
  let loop_cond = wrap_with_left_arrow cond_effects (prefix 2 1 cond_pp vars_pp) in
  let measure = Option.map (fun m -> parens (string "fuel :=" ^^ doc_exp false ctx m)) measure in
  match loop_kind with
  | `While ->
      let loop_head = prefix 2 1 (string "while " ^^ loop_cond) (string "do") in
      let arrow = if body_effects then leftarrowdo else coloneq in
      let loop_body_1 = string "let " ^^ vartuple_pp ^^ space ^^ coloneq ^^ space ^^ vars_pp in
      let loop_body = loop_body_1 ^^ hardline ^^ prefix 2 1 (vars_pp ^^ space ^^ arrow) body_pp in
      let full_loop = prefix 2 1 loop_head loop_body in
      separate hardline [vars_dec_pp; full_loop; wrap_with_pure as_monadic vars_pp]
  | `WhileFuel | `UntilFuel ->
      let measure = Option.get measure in
      let cond_pp = parens (string "fun " ^^ vartuple_pp ^^ string " => " ^^ doc_exp true ctx cond) in
      let init = doc_exp false ctx varstuple in
      let loop_fn = match loop_kind with `WhileFuel -> "whileFuelM" | _ -> "untilFuelM" in
      let loop_head = string loop_fn ^^ space ^^ measure ^^ space ^^ cond_pp ^^ space ^^ init in
      let arrow = if body_effects then leftarrowdo else coloneq in
      let fun_header = string "fun " ^^ vartuple_pp ^^ space ^^ string "=> do" in
      let body_pp = doc_exp true body_ctx body in
      let loop_body = prefix 2 1 fun_header body_pp in
      let full_loop = prefix 2 1 loop_head loop_body in
      let full_loop = string "let" ^^ space ^^ vars_pp ^^ space ^^ leftarrow ^^ space ^^ full_loop in
      separate hardline [full_loop; wrap_with_pure as_monadic vars_pp]
  | `Until ->
      let loop_head = string "repeat" in
      let loop_footer = flow (break 1) [string "until"; loop_cond] in
      let arrow = if body_effects then leftarrowdo else coloneq in
      let loop_body_1 = string "let " ^^ vartuple_pp ^^ space ^^ coloneq ^^ space ^^ vars_pp in
      let loop_body = loop_body_1 ^^ hardline ^^ prefix 2 1 (vars_pp ^^ space ^^ arrow) body_pp in
      let full_loop = prefix 2 1 loop_head loop_body in
      separate hardline [vars_dec_pp; full_loop; loop_footer; wrap_with_pure as_monadic vars_pp]

and doc_exp (as_monadic : bool) ctx (E_aux (e, (l, annot)) as full_exp) =
  let env = env_of_tannot annot in
  let ctx = context_with_env ctx env in
  let d_of_arg ?(with_arrow = true) ctx arg =
    let wrap, arg_monadic =
      match arg with
      | E_aux (arg', _) -> (
          match arg' with
          | E_typ (_, e) when has_effect e -> ((fun x -> wrap_with_do with_arrow true x), true)
          | E_typ (_, e) when has_early_return e -> (parens, false)
          | E_let _ | E_internal_plet _ | E_if _ | E_match _ | E_var _ | E_block _ ->
              if has_effect arg then ((fun x -> wrap_with_do with_arrow true x), true) else (parens, false)
          | _ when has_loop arg -> ((fun x -> wrap_with_do with_arrow true x), true)
          | _ -> ((fun x -> x), not with_arrow) (* for [sailTryCatch] the argument should be a computation *)
        )
    in
    wrap (doc_exp arg_monadic ctx arg)
  in
  let d_of_field (FE_aux (FE_fexp (field, e), _) as fexp) = doc_fexp (has_effect e) ctx fexp in
  let doc_short_circuit lhs when_true when_false =
    let condition = string "if (" ^^ nest 1 (d_of_arg ctx lhs) ^^ string " : Bool)" in
    let branch exp =
      let rendered = doc_exp true ctx exp in
      if has_effect exp then wrap_with_do false true rendered else rendered
    in
    nest 2 condition ^^ hardline
    ^^ prefix 2 1 (string "then") (branch when_true)
    ^^ hardline
    ^^ prefix 2 1 (string "else") (branch when_false)
    |> wrap_with_left_arrow (not as_monadic)
  in
  match e with
  | E_id id ->
      if Env.is_register id env then (
        let register_typ = Env.get_register id env in
        if as_monadic then
          if has_semantic_range ctx register_typ then
            prefix 2 1 (string "do")
              (separate hardline
                 [
                   string "let registerValue " ^^ leftarrow ^^ space ^^ string "readReg " ^^ doc_id_ctor id;
                   string "pure " ^^ parens (doc_semantic_unpack ctx register_typ (string "registerValue"));
                 ]
              )
          else string "readReg " ^^ doc_id_ctor id
        else (
          let value = parens (leftarrow ^^ space ^^ string "readReg " ^^ doc_id_ctor id) in
          if has_semantic_range ctx register_typ then doc_semantic_unpack ctx register_typ value else value
        )
      )
      else (
        let value = doc_id_ctor id in
        let value =
          if global_dependent_binding_unpacked_at_use ctx id (typ_of full_exp) then (
            match Bindings.find_opt id ctx.global.semantic_types.bindings with
            | Some typ -> doc_dependent_unpack ctx typ value
            | None -> value
          )
          else value
        in
        let value =
          match Bindings.find_opt id ctx.global.semantic_types.bindings with
          | Some typ when has_semantic_range ctx typ -> doc_semantic_unpack ctx typ value
          | _ -> value
        in
        wrap_with_pure as_monadic value
      )
  | E_lit l -> wrap_with_pure as_monadic (doc_lit ~width:true l)
  | E_app (Id_aux (Id "None", _), _) -> wrap_with_pure as_monadic (string "none")
  | E_app (Id_aux (Id "Some", _), args) ->
      wrap_with_pure as_monadic
        (let d_id = string "some" in
         let d_args = List.map (d_of_arg ctx) args in
         nest 2 (parens (flow (break 1) (d_id :: d_args)))
        )
  | E_app (Id_aux (Id "__id", _), [e]) -> doc_exp as_monadic ctx e
  | E_app (Id_aux (Id "while#", _), args) -> doc_loop l as_monadic ctx `While args
  | E_app (Id_aux (Id "while#t", _), args) -> doc_loop l as_monadic ctx `WhileFuel args
  | E_app (Id_aux (Id "until#", _), args) -> doc_loop l as_monadic ctx `Until args
  | E_app (Id_aux (Id "until#t", _), args) -> doc_loop l as_monadic ctx `UntilFuel args
  | E_app (f, [lhs; rhs]) when has_effect rhs && Env.is_extern f env "lean" && Env.get_extern f env "lean" = "_lean_and"
    ->
      let false_exp = check_exp env (mk_lit_exp ~loc:l L_false) bool_typ in
      doc_short_circuit lhs rhs false_exp
  | E_app (f, [lhs; rhs]) when has_effect rhs && Env.is_extern f env "lean" && Env.get_extern f env "lean" = "_lean_or"
    ->
      let true_exp = check_exp env (mk_lit_exp ~loc:l L_true) bool_typ in
      doc_short_circuit lhs true_exp rhs
  | E_app (Id_aux (Id "foreach#", _), args) -> (
      match args with
      | [from_exp; to_exp; step_exp; ord_exp; vartuple; body] ->
          let loopvar, body =
            match body with
            | E_aux
                ( E_if
                    ( _,
                      E_aux
                        ( E_let
                            ( ( P_aux (P_typ (_, P_aux (P_var (P_aux (P_id id, _), _), _)), _)
                              | P_aux (P_var (P_aux (P_id id, _), _), _)
                              | P_aux (P_id id, _) ),
                              _,
                              body
                            ),
                          _
                        ),
                      _
                    ),
                  _
                ) ->
                (id, body)
            | _ -> raise (Reporting.err_unreachable l __POS__ ("Unable to find loop variable in " ^ string_of_exp body))
          in
          let from_exp_pp, to_exp_pp, step_exp_pp =
            (doc_exp false ctx from_exp, doc_exp false ctx to_exp, doc_exp false ctx step_exp)
          in
          let step_exp_pp = if is_true ord_exp then step_exp_pp else minus ^^ step_exp_pp in
          let loopvar_pp = doc_id_ctor loopvar in
          let effects = has_effect body in
          let vartuple_pp, body_lambda = make_loop_vars [loopvar_pp] vartuple in
          let body_lambda = if effects then body_lambda ^^ string " do" else body_lambda in
          let vars_pp, body_ctx = name_loop_vars ctx in
          let body_pp = doc_exp (as_monadic && effects) body_ctx body in
          let vars_dec_pp = string "let mut " ^^ vars_pp ^^ string " := " ^^ vartuple_pp in
          let loop_bracket = brackets (separate colon [from_exp_pp; to_exp_pp; step_exp_pp]) ^^ string "i" in
          let loop_head = flow (break 1) [string "for"; loopvar_pp; string "in"; loop_bracket; string "do"] in
          let arrow = if effects then leftarrowdo else coloneq in
          let loop_body_1 = string "let " ^^ vartuple_pp ^^ space ^^ coloneq ^^ space ^^ vars_pp in
          let loop_body = loop_body_1 ^^ hardline ^^ prefix 2 1 (vars_pp ^^ space ^^ arrow) body_pp in
          let full_loop = prefix 2 1 loop_head loop_body in
          separate hardline [vars_dec_pp; full_loop; wrap_with_pure as_monadic vars_pp]
      | _ -> raise (Reporting.err_unreachable l __POS__ "Unexpected number of arguments for loop combinator")
    )
  | E_for (loopvar, from_exp, to_exp, step_exp, Ord_aux (order, _), body) ->
      let combinator = match order with Ord_inc -> "foreach_Z_up" | Ord_dec -> "foreach_Z_down" in
      let from_exp_pp, to_exp_pp, step_exp_pp =
        (doc_exp false ctx from_exp, doc_exp false ctx to_exp, doc_exp false ctx step_exp)
      in
      let step_exp_pp = match order with Ord_inc -> step_exp_pp | Ord_dec -> minus ^^ step_exp_pp in
      let loop_bracket = brackets (separate colon [from_exp_pp; to_exp_pp; step_exp_pp]) ^^ string "i" in
      let loopvar_pp = doc_id_ctor loopvar in
      let body_effect = has_effect body in
      let enter_monad = if body_effect then empty else string "Id.run" in
      let loop_head =
        flow (break 1) (remove_empties [enter_monad; string "for"; loopvar_pp; string "in"; loop_bracket; string "do"])
      in
      let loop_body = doc_exp body_effect ctx body in
      let full_loop = prefix 2 1 loop_head loop_body in
      full_loop
  | E_app ((Id_aux (Id "early_return", _) as f), [arg]) ->
      let throw = if ctx.in_sail_monad then string "SailME.throw " else string "throw " in
      let value = d_of_arg ctx arg in
      let value =
        match ctx.semantic_return with
        | Some typ when has_semantic_range ctx typ -> doc_semantic_pack ctx typ value
        | _ -> value
      in
      let value =
        match (ctx.dependent_result, ctx.dependent_return) with
        | Some result, _ -> doc_prop_dependent_result_pack ctx result arg value
        | None, Some typ when has_dependent_type ctx typ && not (exp_is_ascribed_at ctx typ arg) ->
            doc_dependent_pack ctx typ value
        | _ -> value
      in
      nest 2 (throw ^^ value)
  | E_app (f, args) -> (
      let expected_dependent = ctx.expected_dependent in
      let ctx = { ctx with expected_dependent = None } in
      let _, f_typ = Env.get_val_spec f env in
      let implicits = get_fn_implicits f_typ in
      let instantiation = instantiation_of full_exp in
      let arg_names = Bindings.find_opt f ctx.global.fun_args in
      let arg_names = Option.value ~default:[] arg_names in
      let extern_id = if Env.is_extern f env "lean" then Some (Env.get_extern f env "lean") else None in
      let d_id = Option.fold ~some:string ~none:(doc_id_ctor f) extern_id in
      let raw_args = List.map (d_of_arg ctx) args in
      let semantic_signature = semantic_function_type ctx f in
      let semantic_args, semantic_ret =
        match semantic_signature with
        | Some (args, ret) -> (List.map (subst_unifiers instantiation) args, Some (subst_unifiers instantiation ret))
        | None -> ([], None)
      in
      let arg_bindings, arg_validity_facts, arg_validity_unfold, packed_args =
        try
          let rendered_args =
            List.mapi
              (fun index (typ, (arg_exp, arg)) ->
                let formal_dependent = has_dependent_type ctx typ in
                let formal_prop_dependent_record = prop_dependent_record_typ typ in
                let argument_handles_expected =
                  (formal_dependent || formal_prop_dependent_record)
                  && (app_returns_prop_dependent_record ctx arg_exp || exp_has_dependent_representation ctx arg_exp)
                in
                let arg =
                  if argument_handles_expected then d_of_arg { ctx with expected_dependent = Some typ } arg_exp else arg
                in
                let named_argument_result = prop_dependent_result_of_exp ctx arg_exp in
                let actual_represented = argument_handles_expected || exp_has_dependent_representation ctx arg_exp in
                let representation_typ =
                  if argument_handles_expected then typ else dependent_representation_type ctx arg_exp
                in
                let bindings, validity_facts, validity_unfold, arg =
                  if actual_represented && has_effect arg_exp then (
                    let name = Printf.sprintf "dependentArg%i" index in
                    let value = string name in
                    let binding = string "let " ^^ value ^^ space ^^ coloneq ^^ space ^^ arg in
                    let validity_facts, validity_unfold =
                      match named_argument_result with
                      | Some result ->
                          let carrier_root = parens value ^^ string ".val" in
                          let carrier_facts =
                            List.mapi
                              (fun fact_index property ->
                                string (Printf.sprintf "have dependentArgumentValidity%i_%i := " index fact_index)
                                ^^ property
                              )
                              (prop_dependent_carrier_properties ctx carrier_root result.result_carrier)
                          in
                          ( (string (Printf.sprintf "have dependentArgumentResultValidity%i := " index)
                            ^^ parens value ^^ string ".property"
                            )
                            :: carrier_facts,
                            string (result.result_name ^ ".Valid")
                            :: List.map
                                 (fun record -> doc_id_ctor record ^^ string ".Valid")
                                 (IdSet.elements (prop_dependent_carrier_record_ids ctx result.result_carrier))
                          )
                      | None -> (
                          match prop_dependent_alias_id_for_typ ctx representation_typ with
                          | Some alias -> (
                              match prop_dependent_alias_parts ctx alias with
                              | Some (record, _, _) ->
                                  ( [
                                      string (Printf.sprintf "have dependentArgumentValidity%i := " index)
                                      ^^ parens value ^^ string ".property";
                                    ],
                                    [doc_id_ctor alias ^^ string ".Valid"; doc_id_ctor record ^^ string ".Valid"]
                                  )
                              | None -> ([], [])
                            )
                          | None -> (
                              match prop_dependent_record_id_for_typ representation_typ with
                              | Some record ->
                                  ( [
                                      string (Printf.sprintf "have dependentArgumentValidity%i := " index)
                                      ^^ parens value ^^ string ".property";
                                    ],
                                    [doc_id_ctor record ^^ string ".Valid"]
                                  )
                              | None -> ([], [])
                            )
                        )
                    in
                    ([binding], validity_facts, validity_unfold, value)
                  )
                  else ([], [], [], arg)
                in
                let arg =
                  if formal_dependent then
                    if actual_represented then (
                      match named_argument_result with
                      | Some result ->
                          let carrier_value = parens arg ^^ string ".val" in
                          if dependent_types_equivalent ctx result.result_carrier typ then carrier_value
                          else doc_dependent_repack ctx result.result_carrier typ carrier_value
                      | None ->
                          if not (dependent_types_equivalent ctx representation_typ typ) then (
                            let repacked = doc_dependent_repack ctx representation_typ typ arg in
                            if Option.is_some (prop_dependent_record_id_for_typ typ) then repacked
                            else (
                              let ascription =
                                if contains_prop_dependent_alias ctx typ then doc_dependent_shape ctx typ
                                else doc_raw_typ ctx env typ
                              in
                              parens (separate space [repacked; colon; ascription])
                            )
                          )
                          else arg
                    )
                    else doc_dependent_pack ctx typ arg
                  else if actual_represented then (
                    match named_argument_result with
                    | Some result -> doc_dependent_unpack ctx result.result_carrier (parens arg ^^ string ".val")
                    | None -> doc_dependent_unpack ctx representation_typ arg
                  )
                  else arg
                in
                let arg = if has_semantic_range ctx typ then doc_semantic_pack ctx typ arg else arg in
                (bindings, validity_facts, validity_unfold, arg)
              )
              (List.combine semantic_args (List.combine args raw_args))
          in
          ( List.concat_map (fun (bindings, _, _, _) -> bindings) rendered_args,
            List.concat_map (fun (_, facts, _, _) -> facts) rendered_args,
            List.concat_map (fun (_, _, unfold, _) -> unfold) rendered_args,
            List.map (fun (_, _, _, arg) -> arg) rendered_args
          )
        with Invalid_argument _ -> ([], [], [], raw_args)
      in
      let d_imargs =
        ( match extern_id with
          | Some _ -> []
          | None when Env.is_extern f env "c" -> []
          | None -> (
              match
                ( Bindings.find_opt f ctx.global.semantic_types.valspec_quants,
                  Bindings.find_opt f ctx.global.semantic_types.valspecs
                )
              with
              | Some semantic_quantified, Some semantic_typ ->
                  doc_instantiated_nvars ctx semantic_quantified semantic_typ instantiation
              | _ -> []
            )
          )
        @ doc_implicit_args arg_names implicits packed_args
      in
      let d_args = List.map snd (List.filter (fun x -> not (fst x)) (List.combine implicits packed_args)) in
      let d_constraint_args =
        match
          ( Bindings.find_opt f ctx.global.semantic_types.valspec_quants,
            Bindings.find_opt f !prop_dependent_constraint_kids
          )
        with
        | Some quant, Some relevant_kids ->
            List.filter_map
              (fun (QI_aux (item, _)) ->
                match item with
                | QI_constraint nc when constraint_relevant_to relevant_kids nc ->
                    Some
                      (parens
                         (doc_constraint_proof ~facts:arg_validity_facts ~extra_unfold:arg_validity_unfold ctx
                            (instantiate_constraint instantiation nc)
                         )
                      )
                | _ -> None
              )
              quant
        | _ -> []
      in
      let d_args = d_args @ d_constraint_args in
      let raw_args = List.map snd (List.filter (fun x -> not (fst x)) (List.combine implicits raw_args)) in
      let fn_monadic = not (Effects.function_is_pure f ctx.global.effect_info) in
      let op =
        match op_of_id extern_id with
        | `NotOp
          when extern_id = Some "Int.ediv"
               && List.for_all (fun arg -> typ_is_lean_nat env (typ_of arg)) args
               && typ_is_lean_nat env (typ_of full_exp) ->
            `Binop "/"
        | `Binop "+i"
          when string_of_id f = "add_atom" && List.for_all (fun arg -> typ_is_lean_nat env (typ_of arg)) args ->
            `Binop "+"
        | `Binop "-i"
          when List.for_all (fun arg -> typ_is_lean_nat env (typ_of arg)) args && typ_is_lean_nat env (typ_of full_exp)
          ->
            `Binop "-"
        | op -> op
      in
      match op with
      | `Binop op ->
          let e1 = List.nth raw_args 0 in
          let e2 = List.nth raw_args 1 in
          let res = e1 ^^ space ^^ string op ^^ space ^^ e2 in
          wrap_with_pure as_monadic (parens res) |> nest 2
      | `Unop op ->
          let e = List.nth raw_args 0 in
          let res = string op ^^ space ^^ e in
          wrap_with_pure as_monadic (parens res) |> nest 2
      | `NotOp ->
          let call = parens (flow (break 1) ((d_id :: d_imargs) @ d_args)) in
          let result_transform =
            match semantic_ret with
            | Some ret ->
                let public_typ = Option.value ~default:(typ_of full_exp) expected_dependent in
                let public_dependent = has_dependent_type ctx public_typ in
                let ret_dependent = has_dependent_type ctx ret in
                let named_result_matches_public =
                  match prop_dependent_result_for_id ctx f with
                  | Some _ when Option.is_none expected_dependent -> true
                  | Some result -> (
                      try Type_check.alpha_equivalent ctx.env result.result_typ public_typ
                      with Type_internal.Type_error _ -> false
                    )
                  | None -> false
                in
                let () =
                  if debug_dependent_representation && (public_dependent || ret_dependent) then
                    Printf.eprintf
                      "lean-dependent-call: function=%s expression=%s return=%s public=%s argument-bindings=%d \
                       bound={%s} constraints={%s}\n\
                       %!"
                      (string_of_id f) (string_of_exp full_exp) (string_of_typ ret) (string_of_typ public_typ)
                      (List.length arg_bindings)
                      (String.concat "," (List.map string_of_kid (KidSet.elements ctx.lean_bound_nvars)))
                      (String.concat "," (List.map string_of_n_constraint (Env.get_constraints ctx.env)))
                in
                let pack_public value =
                  let public_ascription =
                    if public_dependent then doc_dependent_shape ctx public_typ else doc_raw_typ ctx env public_typ
                  in
                  parens (separate space [doc_dependent_pack ctx public_typ value; colon; public_ascription])
                in
                let dependent_transform =
                  match (ret_dependent, public_dependent) with
                  | true, false -> Some (fun value -> doc_dependent_unpack ctx ret value)
                  | false, true -> Some pack_public
                  | true, true
                    when prop_dependent_mode_active () && (not named_result_matches_public)
                         && not (dependent_types_equivalent ctx ret public_typ) ->
                      Some (fun value -> doc_dependent_repack ctx ret public_typ value)
                  (* Unpacking and repacking is the identity when the call
                     already returns the expected shape, and Lean cannot
                     elaborate the destructuring lambdas that spell it out. *)
                  | true, true
                    when arg_bindings <> [] && (not named_result_matches_public)
                         && not (dependent_types_equivalent ctx ret public_typ) ->
                      Some (fun value -> pack_public (doc_dependent_unpack ctx ret value))
                  | _ -> None
                in
                let semantic = has_semantic_range ctx ret in
                if Option.is_some dependent_transform || semantic then
                  Some
                    (fun value ->
                      let value =
                        Option.fold ~none:value ~some:(fun transform -> transform value) dependent_transform
                      in
                      if semantic then doc_semantic_unpack ctx ret value else value
                    )
                else None
            | None -> None
          in
          let call =
            if arg_bindings <> [] then (
              let result =
                match (fn_monadic, result_transform) with
                | true, Some transform ->
                    [
                      string "let publicResult " ^^ leftarrow ^^ space ^^ call;
                      string "pure " ^^ parens (transform (string "publicResult"));
                    ]
                | true, None -> [call]
                | false, Some transform -> [string "pure " ^^ parens (transform call)]
                | false, None -> [string "pure " ^^ parens call]
              in
              wrap_with_do (not as_monadic) true (separate hardline (arg_bindings @ result))
            )
            else (
              match result_transform with
              | Some transform ->
                  if fn_monadic then
                    if as_monadic then
                      parens
                        (prefix 2 1 (string "do")
                           (separate hardline
                              [
                                string "let publicResult " ^^ leftarrow ^^ space ^^ call;
                                string "pure " ^^ parens (transform (string "publicResult"));
                              ]
                           )
                        )
                    else transform (parens (leftarrow ^^ space ^^ call))
                  else wrap_with_pure as_monadic (transform call)
              | _ ->
                  wrap_with_left_arrow ((not as_monadic) && fn_monadic)
                    (wrap_with_pure (as_monadic && not fn_monadic) call)
            )
          in
          nest 2 call
    )
  | E_vector vals ->
      if is_bitvector_typ (typ_of full_exp) then
        nest 2
          (wrap_with_pure as_monadic
             (parens (flow space [string "BitVec.join1"; brackets (separate_map comma_sp (d_of_arg ctx) vals)]))
          )
      else
        string "#v"
        ^^ wrap_with_pure as_monadic (brackets (nest 2 (separate_map comma_sp (d_of_arg ctx) (List.rev vals))))
  | E_typ (typ, e) ->
      let typ =
        let same_prop_dependent_alias candidate =
          match (prop_dependent_alias_id_for_typ ctx typ, prop_dependent_alias_id_for_typ ctx candidate) with
          | Some actual, Some expected when Id.compare actual expected = 0 -> (
              try
                Type_check.alpha_equivalent ctx.env
                  (expand_synonyms_for_dependent_type ctx typ)
                  (expand_synonyms_for_dependent_type ctx candidate)
              with Type_internal.Type_error _ -> false
            )
          | _ -> false
        in
        match ctx.expected_dependent with
        | Some expected when same_prop_dependent_alias expected -> expected
        | Some expected
          when has_dependent_type ctx expected && app_returns_prop_dependent_record ctx e
               && dependent_types_equivalent ctx expected (dependent_representation_type ctx e) ->
            expected
        | _ -> (
            match ctx.dependent_return with
            | Some expected when same_prop_dependent_alias expected -> expected
            | _ -> typ
          )
      in
      let active_result =
        match ctx.dependent_result with
        | Some result when Type_check.alpha_equivalent ctx.env typ result.result_typ -> Some result
        | _ -> None
      in
      let target_dependent = has_dependent_type ctx typ in
      let expression_handles_expected =
        Option.is_none active_result && target_dependent && app_returns_prop_dependent_record ctx e
      in
      let expression_handles_result_carrier = Option.is_some active_result && app_returns_prop_dependent_record ctx e in
      let represented = expression_handles_expected || exp_has_dependent_representation ctx e in
      let representation_typ = if expression_handles_expected then typ else dependent_representation_type ctx e in
      let expression_ctx =
        {
          ctx with
          expected_dependent =
            ( if
                expression_handles_expected
                || (target_dependent && represented && dependent_types_equivalent ctx representation_typ typ)
              then Some typ
              else (
                match active_result with
                | Some _ when expression_handles_result_carrier -> Some (dependent_representation_type ctx e)
                | _ -> None
              )
            );
        }
      in
      let needs_repack =
        target_dependent && represented && not (dependent_types_equivalent ctx representation_typ typ)
      in
      let already_named_result =
        match (active_result, prop_dependent_result_of_exp ctx e) with
        | Some expected, Some actual -> String.equal expected.result_name actual.result_name
        | _ -> false
      in
      let should_pack =
        match active_result with
        | Some _ -> not already_named_result
        | None -> target_dependent && ((not represented) || needs_repack)
      in
      let pack_expected value =
        (* Sail's flow typing refined the carrier's indices under a branch
           test; Lean only has that test as a Bool equation, so the carrier is
           cast under it before the witnesses are packed around it. *)
        let value =
          if existential_pack_refines_index ctx typ (typ_of e) then doc_index_refinement_cast value else value
        in
        let packed =
          match active_result with
          | Some result -> doc_prop_dependent_result_pack ctx result e value
          | None ->
              if needs_repack then doc_dependent_repack ctx representation_typ typ value
              else doc_dependent_pack ctx typ value
        in
        let expected_typ =
          match active_result with
          | Some result -> doc_prop_dependent_result_type ctx result
          | None ->
              if contains_prop_dependent_alias ctx typ then doc_dependent_shape ctx typ
              else doc_raw_typ ctx (env_of full_exp) typ
        in
        parens (separate space [packed; colon; expected_typ])
      in
      let () =
        if target_dependent then log_dependent_representation typ e represented representation_typ needs_repack
      in
      let refines_index = (not target_dependent) && index_refined_record_typ ctx typ (typ_of e) in
      (* A tuple literal is not a single carrier: each component chooses its
         own representation, and only some of them may still need packing.
         Distribute the expected type over the components so that each one is
         packed, unpacked or left alone on its own terms. *)
      let component_annotated_tuple =
        if target_dependent && Option.is_none active_result then (
          match (e, expand_synonyms_for_dependent_type ctx typ) with
          | E_aux (E_tuple components, tuple_annot), Typ_aux (Typ_tuple component_typs, _)
            when List.length components = List.length component_typs ->
              Some
                (E_aux
                   ( E_tuple
                       (List.map2
                          (fun component_typ (E_aux (_, component_annot) as component) ->
                            E_aux (E_typ (component_typ, component), component_annot)
                          )
                          component_typs components
                       ),
                     tuple_annot
                   )
                )
          | _ -> None
        )
        else None
      in
      if target_dependent && expression_never_returns e then
        doc_exp as_monadic { expression_ctx with expected_dependent = None } e
      else if
        target_dependent
        && match e with E_aux ((E_if _ | E_match _ | E_let _ | E_internal_plet _ | E_block _), _) -> true | _ -> false
      then doc_exp as_monadic ctx (annotate_dependent_tail typ e)
      else if Option.is_some component_annotated_tuple then
        doc_exp as_monadic { ctx with expected_dependent = None } (Option.get component_annotated_tuple)
      else if has_effect e then
        if should_pack then (
          let computation =
            parens
              (prefix 2 1 (string "do")
                 (separate hardline
                    [
                      string "let dependentResult " ^^ leftarrow ^^ space ^^ doc_exp true expression_ctx e;
                      string "pure " ^^ parens (pack_expected (string "dependentResult"));
                    ]
                 )
              )
          in
          if as_monadic then computation else parens (leftarrow ^^ space ^^ computation)
        )
        else if refines_index then (
          let computation =
            parens
              (prefix 2 1 (string "do")
                 (separate hardline
                    [
                      string "let indexRefinedResult " ^^ leftarrow ^^ space ^^ doc_exp true expression_ctx e;
                      string "pure " ^^ doc_index_refinement_cast (string "indexRefinedResult");
                    ]
                 )
              )
          in
          if as_monadic then computation else parens (leftarrow ^^ space ^^ computation)
        )
        else doc_exp as_monadic expression_ctx e
      else (
        let value = doc_exp false expression_ctx e in
        let value = if refines_index then doc_index_refinement_cast value else value in
        let value = if should_pack then pack_expected value else value in
        let expected_typ =
          match active_result with
          | Some result -> doc_prop_dependent_result_type ctx result
          | None ->
              if contains_prop_dependent_alias ctx typ then doc_dependent_shape ctx typ
              else doc_raw_typ ctx (env_of full_exp) typ
        in
        wrap_with_pure as_monadic (parens (separate space [value; colon; expected_typ]))
      )
  | E_tuple es ->
      (* An expected tuple type belongs to the tuple, never to a component:
         a component that inherited it would pack itself as the whole tuple. *)
      let component_ctx = { ctx with expected_dependent = None } in
      wrap_with_pure as_monadic (parens (separate_map (comma ^^ space) (d_of_arg component_ctx) es))
  (* Sail's flow typing carries the negated condition past a guard such as
       if invalid then throw;
     Keep the continuation in the corresponding Lean branch so that the
     dependent-if hypothesis remains in scope for generated validity proofs. *)
  | E_let (lpat, E_aux (E_if (condition, then_exp, else_exp), _), body)
  | E_internal_plet (lpat, E_aux (E_if (condition, then_exp, else_exp), _), body)
    when is_anonymous_pat lpat && expression_never_returns then_exp && expression_is_unit_value else_exp ->
      doc_exp as_monadic ctx (E_aux (E_if (condition, then_exp, body), (l, annot)))
  | E_let (lpat, E_aux (E_if (condition, then_exp, else_exp), _), body)
  | E_internal_plet (lpat, E_aux (E_if (condition, then_exp, else_exp), _), body)
    when is_anonymous_pat lpat && expression_is_unit_value then_exp && expression_never_returns else_exp ->
      doc_exp as_monadic ctx (E_aux (E_if (condition, body, else_exp), (l, annot)))
  | E_let (lpat, lexp, e') | E_internal_plet (lpat, lexp, e') ->
      let has_loop = has_loop lexp in
      let is_arrow_do = match e with E_let _ when not has_loop -> false | _ -> true in
      let lexp_typ = typ_of lexp in
      let named_result = prop_dependent_result_of_exp ctx lexp in
      let binding_typ =
        match named_result with
        | Some result -> result.result_carrier
        | None -> if exp_has_dependent_representation ctx lexp then dependent_representation_type ctx lexp else lexp_typ
      in
      let explicit_prop_target =
        match lpat with
        | P_aux (P_typ (target_typ, _), _)
          when prop_dependent_alias_for_typ ctx target_typ && not (pattern_destructures_value lpat) ->
            Some target_typ
        | _ -> None
      in
      let binding_typ = Option.value ~default:binding_typ explicit_prop_target in
      let preserve_prop_dependent =
        Option.is_none named_result
        && (not (pattern_destructures_value lpat))
        && (prop_dependent_alias_for_typ ctx binding_typ || prop_dependent_record_typ binding_typ)
      in
      let pattern_kid_docs = existential_pattern_kid_docs ctx binding_typ lpat in
      let pattern_ctx = context_with_pattern_kid_docs ctx pattern_kid_docs in
      let pattern_projection_ctx =
        add_existential_carrier_witness_docs pattern_ctx binding_typ
          [lexp_typ; typ_of_pat lpat]
          (fun _ witness -> doc_kid pattern_ctx witness)
      in
      let pattern_projection_kid_docs = pattern_projection_ctx.kid_docs in
      let id_typ =
        let pattern = doc_pat_for_type (context_with_env pattern_ctx (env_of lexp)) false binding_typ lpat in
        match named_result with
        | Some _ when pattern_destructures_value lpat -> string "⟨" ^^ pattern ^^ comma_sp ^^ string "_sailValidity⟩"
        | Some _ -> pattern
        | None ->
            if pattern_destructures_value lpat || preserve_prop_dependent then pattern
            else doc_dependent_pattern ctx binding_typ pattern
      in
      let typ_ascription =
        match doc_pat_typ_ascription ctx lpat with
        | Some _ as explicit -> explicit
        | None
          when prop_dependent_mode_active ()
               && (has_effect lexp || has_loop)
               && (not (has_dependent_type ctx binding_typ))
               && match lpat with P_aux (P_id id, _) -> not (is_enum (env_of_pat lpat) id) | _ -> false ->
            let indexed_named_type =
              match binding_typ with
              | Typ_aux (Typ_app (_, args), _) ->
                  List.exists
                    (fun (A_aux (arg, _)) -> match arg with A_nexp _ | A_bool _ -> true | A_typ _ -> false)
                    args
              | _ -> false
            in
            if not indexed_named_type then None
            else
              Some
                ( match named_result with
                | Some result -> doc_prop_dependent_result_type ctx result
                | None when contains_prop_dependent_alias ctx binding_typ -> doc_dependent_shape ctx binding_typ
                | None -> doc_raw_typ ctx (env_of lexp) binding_typ
                )
        | None -> None
      in
      let lexp =
        match lpat with
        | P_aux (P_typ (target_typ, _), _) when has_top_level_dependent_type ctx target_typ ->
            let (E_aux (_, lexp_annot)) = lexp in
            E_aux (E_typ (target_typ, lexp), lexp_annot)
        | _ -> lexp
      in
      let bound_ids = pat_ids lpat in
      let packed_target =
        match lpat with
        | P_aux (P_typ (target_typ, _), _)
          when has_top_level_dependent_type ctx target_typ && not (pattern_destructures_value lpat) ->
            Some target_typ
        | _ -> None
      in
      let locally_bound_nvars =
        if Option.is_none named_result && pattern_destructures_value lpat then (
          match expand_synonyms_for_dependent_type ctx binding_typ with
          | Typ_aux (Typ_exist (kopts, _, inner), _) ->
              KidSet.of_list (List.map kopt_kid (relevant_existential_kopts kopts inner))
          | _ -> KidSet.empty
        )
        else KidSet.empty
      in
      let nested_packed_bindings =
        match named_result with
        | Some _ when pattern_destructures_value lpat -> nested_dependent_pattern_bindings ctx binding_typ lpat
        | Some _ -> Bindings.empty
        | None ->
            if has_top_level_dependent_type ctx binding_typ then Bindings.empty
            else nested_dependent_pattern_bindings ctx binding_typ lpat
      in
      let lexp_ctx = ctx in
      let ctx = update_ctx_pat ctx lpat in
      let ctx = { ctx with local_let_ids = IdSet.union bound_ids ctx.local_let_ids } in
      let ctx =
        if KBindings.is_empty pattern_kid_docs then ctx
        else
          {
            ctx with
            dependent_pattern_kid_docs =
              IdSet.fold
                (fun id bindings -> Bindings.add id pattern_projection_kid_docs bindings)
                bound_ids ctx.dependent_pattern_kid_docs;
          }
      in
      let ctx = { ctx with lean_bound_nvars = KidSet.union ctx.lean_bound_nvars locally_bound_nvars } in
      let ctx =
        if
          Option.is_none named_result && pattern_destructures_value lpat && has_top_level_dependent_type ctx binding_typ
        then
          add_existential_carrier_witness_docs ctx binding_typ
            [lexp_typ; typ_of_pat lpat]
            (fun _ witness -> doc_kid ctx witness)
        else ctx
      in
      let ctx =
        Bindings.fold
          (fun id typ ctx ->
            {
              ctx with
              unpacked_dependent_ids = IdSet.remove id ctx.unpacked_dependent_ids;
              packed_dependent_types = Bindings.add id typ ctx.packed_dependent_types;
              packed_dependent_results = Bindings.remove id ctx.packed_dependent_results;
            }
          )
          nested_packed_bindings ctx
      in
      let ctx =
        match named_result with
        | Some result when not (pattern_destructures_value lpat) ->
            {
              ctx with
              unpacked_dependent_ids =
                IdSet.fold (fun id ids -> IdSet.remove id ids) bound_ids ctx.unpacked_dependent_ids;
              packed_dependent_types =
                IdSet.fold (fun id bindings -> Bindings.remove id bindings) bound_ids ctx.packed_dependent_types;
              packed_dependent_results =
                IdSet.fold (fun id bindings -> Bindings.add id result bindings) bound_ids ctx.packed_dependent_results;
            }
        | Some _ ->
            {
              ctx with
              packed_dependent_results =
                IdSet.fold (fun id bindings -> Bindings.remove id bindings) bound_ids ctx.packed_dependent_results;
            }
        | None when has_top_level_dependent_type ctx binding_typ && not preserve_prop_dependent ->
            {
              ctx with
              unpacked_dependent_ids = IdSet.union ctx.unpacked_dependent_ids bound_ids;
              packed_dependent_types =
                IdSet.fold (fun id bindings -> Bindings.remove id bindings) bound_ids ctx.packed_dependent_types;
            }
        | None when preserve_prop_dependent ->
            {
              ctx with
              unpacked_dependent_ids =
                IdSet.fold (fun id ids -> IdSet.remove id ids) bound_ids ctx.unpacked_dependent_ids;
              packed_dependent_types =
                IdSet.fold
                  (fun id bindings -> Bindings.add id binding_typ bindings)
                  bound_ids ctx.packed_dependent_types;
            }
        | None -> (
            match packed_target with
            | Some target_typ -> (
                let ctx =
                  {
                    ctx with
                    unpacked_dependent_ids =
                      IdSet.fold (fun id ids -> IdSet.remove id ids) bound_ids ctx.unpacked_dependent_ids;
                    packed_dependent_types =
                      IdSet.fold
                        (fun id bindings -> Bindings.add id target_typ bindings)
                        bound_ids ctx.packed_dependent_types;
                  }
                in
                match IdSet.elements bound_ids with
                | [id] ->
                    let rec witness_path value index =
                      if index = 0 then parens value ^^ string ".1"
                      else witness_path (parens value ^^ string ".2") (index - 1)
                    in
                    add_existential_carrier_witness_docs ctx target_typ
                      [lexp_typ; typ_of_pat lpat]
                      (fun index _ -> witness_path (doc_id_ctor id) index)
                | _ -> ctx
              )
            | None -> ctx
          )
      in
      let pp_let_line_f l = group (nest 2 (flow (break 1) l)) in
      let pp_let_line =
        if has_effect lexp || has_loop then
          if is_unit (typ_of lexp) && is_anonymous_pat lpat then doc_exp true lexp_ctx lexp
          else (
            match (is_arrow_do, typ_ascription) with
            | true, None ->
                pp_let_line_f [separate space [string "let"; id_typ; leftarrowdo]; doc_exp true lexp_ctx lexp]
            | false, None ->
                pp_let_line_f [separate space [string "let"; id_typ; leftarrow]; doc_exp true lexp_ctx lexp]
            | true, Some asc ->
                pp_let_line_f
                  ([
                     separate space [string "let"; id_typ; leftarrow; string "(("; string "do"];
                     doc_exp true lexp_ctx lexp;
                     string ")";
                     colon;
                   ]
                  @ prepend_monad lexp_ctx lexp asc
                  @ [string ")"]
                  )
            | false, Some asc ->
                pp_let_line_f
                  ([
                     separate space [string "let"; id_typ; leftarrow; string "(("];
                     doc_exp true lexp_ctx lexp;
                     string ")";
                     colon;
                   ]
                  @ prepend_monad lexp_ctx lexp asc
                  @ [string ")"]
                  )
          )
        else (
          match typ_ascription with
          | Some asc ->
              pp_let_line_f [separate space [string "let"; id_typ; colon; asc; coloneq]; doc_exp false lexp_ctx lexp]
          | None -> pp_let_line_f [separate space [string "let"; id_typ; coloneq]; doc_exp false lexp_ctx lexp]
        )
      in
      pp_let_line ^^ hardline ^^ doc_exp as_monadic ctx e'
  | E_internal_return e -> doc_exp false ctx e (* ??? *)
  | E_struct (struct_name, fexps) ->
      let record_id = match struct_name with SN_id id -> Some id | SN_anon -> record_id_of_typ (typ_of full_exp) in
      (* Fields projected from the record's indices are not stored, so the
         literal must not mention them.  Their Sail value is the index the
         result type already carries. *)
      let fexps = projected_fields_removed ctx record_id fexps in
      let args =
        List.map
          (fun (FE_aux (FE_fexp (field, _), _) as fexp) ->
            let field_typ = Option.bind record_id (fun record_id -> semantic_record_field ctx record_id field) in
            doc_fexp ?field_typ (has_effect (match fexp with FE_aux (FE_fexp (_, e), _) -> e)) ctx fexp
          )
          fexps
      in
      wrap_with_pure as_monadic (braces (space ^^ align (separate (comma ^^ hardline) args) ^^ space))
  | E_field (exp, id) ->
      let rec record_root_id = function
        | E_aux (E_id record_id, _) -> Some record_id
        | E_aux (E_field (record, _), _) | E_aux (E_typ (_, record), _) | E_aux (E_block [record], _) ->
            record_root_id record
        | _ -> None
      in
      let root_id = record_root_id exp in
      let has_record_witnesses =
        match root_id with Some record_id -> Bindings.mem record_id ctx.dependent_pattern_kid_docs | None -> false
      in
      let use_singleton_index =
        match root_id with
        | Some record_id
          when (IdSet.mem record_id ctx.unpacked_dependent_ids || IdSet.mem record_id ctx.local_let_ids)
               && not has_record_witnesses ->
            false
        | _ -> true
      in
      let projection_ctx =
        match root_id with
        | Some record_id -> (
            match Bindings.find_opt record_id ctx.dependent_pattern_kid_docs with
            | Some docs -> context_with_pattern_kid_docs ctx docs
            | None -> ctx
          )
        | _ -> ctx
      in
      let field =
        match if use_singleton_index then singleton_nexp_of_typ projection_ctx (typ_of full_exp) else None with
        | Some nexp -> doc_nexp projection_ctx nexp
        | None -> (
            let record = doc_exp false ctx exp in
            let record =
              if exp_has_dependent_representation ctx exp then
                doc_dependent_unpack ctx (dependent_representation_type ctx exp) record
              else record
            in
            let field = record ^^ dot ^^ doc_id_ctor id in
            match semantic_record_field_of_exp ctx exp id with
            | Some typ when exp_has_dependent_representation ctx exp && contains_prop_dependent_alias ctx typ ->
                parens (doc_dependent_pack ctx typ field ^^ space ^^ colon ^^ space ^^ doc_dependent_shape ctx typ)
            | Some typ when has_semantic_range ctx typ -> doc_semantic_unpack ctx typ field
            | _ ->
                let typ = typ_of full_exp in
                if exp_has_dependent_representation ctx exp && contains_prop_dependent_alias ctx typ then
                  parens (doc_dependent_pack ctx typ field ^^ space ^^ colon ^^ space ^^ doc_dependent_shape ctx typ)
                else field
          )
      in
      wrap_with_pure as_monadic field
  | E_struct_update (exp, fexps) ->
      let record_id = record_id_of_typ (typ_of exp) in
      let updated = projected_fields_removed ctx record_id fexps in
      let args =
        List.map
          (fun (FE_aux (FE_fexp (field, e), _) as fexp) ->
            let field_typ = Option.bind record_id (fun record_id -> semantic_record_field ctx record_id field) in
            doc_fexp ?field_typ (has_effect e) ctx fexp
          )
          updated
      in
      let record = doc_exp false ctx exp in
      let record =
        if has_top_level_dependent_type ctx (typ_of exp) then doc_dependent_unpack ctx (typ_of exp) record else record
      in
      (* An update that only rewrites projected fields changes the record's
         indices and nothing else, so the whole update is the original value
         re-indexed. *)
      if args = [] then
        wrap_with_pure as_monadic
          (if List.length updated = List.length fexps then record else doc_index_refinement_cast record)
      else
        wrap_with_pure as_monadic
          (braces (space ^^ record ^^ string " with " ^^ separate (comma ^^ space) args ^^ space))
  | E_match (discr, brs) ->
      let brs =
        if has_dependent_type ctx (typ_of full_exp) then
          List.map
            (fun (Pat_aux (clause, clause_annot)) ->
              match clause with
              | Pat_exp (pat, branch) ->
                  Pat_aux (Pat_exp (pat, annotate_dependent_tail (typ_of full_exp) branch), clause_annot)
              | Pat_when (pat, guard, branch) ->
                  Pat_aux (Pat_when (pat, guard, annotate_dependent_tail (typ_of full_exp) branch), clause_annot)
            )
            brs
        else brs
      in
      let is_match_bv = is_match_bv brs in
      let as_monadic' =
        List.exists (fun x -> effectful (effect_of_annot (match x with Pat_aux (_, (_, annot)) -> annot))) brs
        || as_monadic
      in
      let cases = separate_map hardline (doc_match_clause is_match_bv as_monadic' ctx) brs in
      string (match_or_match_bv is_match_bv brs) ^^ d_of_arg ctx discr ^^ string " with" ^^ hardline ^^ cases
  | E_assign ((LE_aux (le_act, tannot) as le), e) ->
      wrap_with_left_arrow (not as_monadic)
        ( match le_act with
        | LE_id id | LE_typ (_, id) ->
            let value = d_of_arg ctx e in
            let value =
              if Env.is_register id env then (
                let register_typ = Env.get_register id env in
                let value =
                  if has_top_level_dependent_type ctx register_typ then
                    if exp_has_dependent_representation ctx e then (
                      let representation_typ = dependent_representation_type ctx e in
                      if dependent_types_equivalent ctx representation_typ register_typ then value
                      else doc_dependent_repack ctx representation_typ register_typ value
                    )
                    else doc_dependent_pack ctx register_typ value
                  else value
                in
                if has_semantic_range ctx register_typ then doc_semantic_pack ctx register_typ value else value
              )
              else value
            in
            string "writeReg " ^^ doc_id_ctor id ^^ space ^^ value
        | LE_deref e' -> string "writeRegRef " ^^ d_of_arg ctx e' ^^ space ^^ d_of_arg ctx e
        | _ -> failwith ("assign " ^ string_of_lexp le ^ "not implemented yet")
        )
  | E_if (i, t, e) ->
      let index_refined branch = index_refined_record_typ ctx (typ_of full_exp) (typ_of branch) in
      let refines_index = index_refined t || index_refined e in
      let t, e =
        if has_dependent_type ctx (typ_of full_exp) then
          (annotate_dependent_tail (typ_of full_exp) t, annotate_dependent_tail (typ_of full_exp) e)
        else if refines_index then
          ( (if index_refined t then annotate_dependent_tail (typ_of full_exp) t else t),
            if index_refined e then annotate_dependent_tail (typ_of full_exp) e else e
          )
        else (t, e)
      in
      let statements_monadic = as_monadic || has_effect t || has_effect e in
      let condition =
        if has_dependent_type ctx (typ_of full_exp) || refines_index then
          string "if " ^^ name_if_hypothesis ctx ^^ string " : (" ^^ nest 1 (d_of_arg ctx i) ^^ string " : Bool) = true"
        else string "if (" ^^ nest 1 (d_of_arg ctx i) ^^ string " : Bool)"
      in
      nest 2 condition ^^ hardline
      ^^ prefix 2 1 (string "then") (wrap_exp statements_monadic ctx t)
      ^^ hardline
      ^^ prefix 2 1 (string "else") (wrap_exp statements_monadic ctx e)
      |> wrap_with_left_arrow (statements_monadic && not as_monadic)
  | E_ref id -> parens (string ".Reg " ^^ doc_id_ctor id)
  | E_exit _ -> string "throw Error.Exit"
  | E_throw e ->
      let arrow = if as_monadic then empty else leftarrow in
      arrow ^^ string "sailThrow " ^^ parens (doc_exp false ctx e)
  | E_try (e, cases) ->
      let x = E_aux (E_id (Id_aux (Id "the_exception", Unknown)), (Unknown, annot)) in
      let cases = nest 2 (doc_exp true ctx (E_aux (E_match (x, cases), (Unknown, annot)))) in
      let try_catch = if has_early_return e then string "sailTryCatchE " else string "sailTryCatch " in
      let arrow = if as_monadic then empty else leftarrow in
      nest 2
        (arrow ^^ try_catch
        ^^ parens (d_of_arg ~with_arrow:false ctx e)
        ^^ space
        ^^ parens (string "fun the_exception => " ^^ hardline ^^ cases)
        )
  | E_assert (e1, e2) -> string "assert " ^^ d_of_arg ctx e1 ^^ space ^^ d_of_arg ctx e2
  | E_list es -> wrap_with_pure as_monadic (brackets (separate_map comma_sp (d_of_arg ctx) es))
  | E_cons (hd_e, tl_e) ->
      wrap_with_pure as_monadic (parens (separate space [d_of_arg ctx hd_e; string "::"; d_of_arg ctx tl_e]))
  | _ -> failwith ("Expression " ^ string_of_exp_con full_exp ^ " " ^ string_of_exp full_exp ^ " not translatable yet.")

and doc_fexp ?field_typ with_arrow ctx (FE_aux (FE_fexp (field, e), _)) =
  let expression_ctx =
    match field_typ with
    | Some typ
      when has_top_level_dependent_type ctx typ
           && (prop_dependent_mode_active () || exp_has_dependent_representation ctx e) ->
        { ctx with expected_dependent = Some typ }
    | _ -> ctx
  in
  let value = doc_exp with_arrow expression_ctx e in
  let arrow, value =
    match field_typ with
    | Some typ when prop_dependent_record_typ typ ->
        let value =
          if exp_has_dependent_representation ctx e then
            doc_dependent_unpack ctx (dependent_representation_type ctx e) value
          else value
        in
        ((if with_arrow then leftarrow ^^ space else empty), value)
    | Some typ when has_semantic_range ctx typ || has_top_level_dependent_type ctx typ ->
        let pack value =
          let value =
            if has_top_level_dependent_type ctx typ then
              if exp_has_dependent_representation ctx e then (
                let representation_typ = dependent_representation_type ctx e in
                if dependent_types_equivalent ctx representation_typ typ then value
                else doc_dependent_repack ctx representation_typ typ value
              )
              else doc_dependent_pack ctx typ value
            else value
          in
          if has_semantic_range ctx typ then doc_semantic_pack ctx typ value else value
        in
        if with_arrow then
          ( leftarrow ^^ space,
            prefix 2 1 (string "do")
              (separate hardline
                 [
                   string "let publicField " ^^ leftarrow ^^ space ^^ value;
                   string "pure " ^^ parens (pack (string "publicField"));
                 ]
              )
          )
        else (empty, pack value)
    | _ -> ((if with_arrow then leftarrow ^^ space else empty), value)
  in
  doc_id_ctor field ^^ string " := " ^^ arrow ^^ nest 2 value

let doc_binder ctx i t =
  let parenthesizer =
    match t with
    | Typ_aux (Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]), _) ->
        implicit_parens
    | _ -> parens
  in
  (* Overwrite the id if it's captured *)
  let ctx = match captured_typ_var (i, t) with Some (i, ki) -> add_single_kid_id_rename ctx i ki | _ -> ctx in
  let typ = if prop_dependent_record_typ t then doc_dependent_shape ctx t else doc_typ ctx t in
  (ctx, separate space [doc_id_ctor i; colon; typ] |> parenthesizer)

(** Find all patterns in the arguments of the sail function that Lean cannot handle in a [def], and add them as let
    bindings in the prelude of the translation of the function. This assumes that the pattern is irrefutable. *)
let add_function_pattern ctx fixup_binders (P_aux (pat, pat_annot) as pat_full) var typ =
  match pat with
  | P_id _ | P_typ (_, P_aux (P_id _, _)) | P_tuple [] | P_lit _ | P_wild -> fixup_binders
  | _ ->
      fun (E_aux (_, body_annot) as body : tannot exp) ->
        E_aux (E_let (pat_full, E_aux (E_id var, (Unknown, mk_tannot ctx.env typ)), body), body_annot) |> fixup_binders

(** Find all the [int] and [atom] types in the function pattern and express them as paths that use the lean variables,
    so that we can use them in the return type of the function. For example, see the function [two_tuples_atom] in the
    test case test/lean/typquant.sail. *)
let rec add_path_renamings ~path ctx (P_aux (pat, pat_annot)) (Typ_aux (typ, typ_annot) as typ_full) =
  match (pat, typ) with
  | P_tuple pats, Typ_tuple typs ->
      List.fold_left
        (fun (ctx, i) (pat, typ) -> (add_path_renamings ~path:(Printf.sprintf "%s.%i" path i) ctx pat typ, i + 1))
        (ctx, 1) (List.combine pats typs)
      |> fst
  | P_id id, typ -> (
      match captured_typ_var (id, typ_full) with
      | Some (_, kid) -> add_single_kid_id_rename ctx (mk_id path) kid
      | None -> ctx
    )
  | _ -> ctx

(* Plain dependent values are nested Sigma pairs.  Name their witnesses before
   the function prelude shadows a public argument with its carrier, so Sail
   singleton projections keep using the indices encoded by the Sigma type. *)
let dependent_binder_witnesses ctx binder public_typ raw_typ pattern_typ =
  let rec collect ctx value_path witness_index typ =
    let typ = expand_synonyms_for_dependent_type ctx typ in
    match typ with
    | Typ_aux (Typ_exist (kopts, _, inner), _) ->
        let relevant = relevant_existential_kopts kopts inner in
        let ctx, bindings, value_path, witness_index =
          List.fold_left
            (fun (ctx, bindings, value_path, witness_index) (KOpt_aux (KOpt_kind (_, kid), _)) ->
              let witness = Printf.sprintf "%s_dependentWitness%i" (fix_id (string_of_id binder)) witness_index in
              let binding = separate space [string "let"; string witness; coloneq; parens value_path ^^ string ".1"] in
              ( { ctx with kid_docs = KBindings.add kid (string witness) ctx.kid_docs },
                bindings @ [binding],
                parens value_path ^^ string ".2",
                witness_index + 1
              )
            )
            (ctx, [], value_path, witness_index) relevant
        in
        let ctx, nested, _, witness_index = collect ctx value_path witness_index inner in
        (ctx, bindings @ nested, value_path, witness_index)
    | _ -> (ctx, [], value_path, witness_index)
  in
  let ctx, bindings, _, _ = collect ctx (doc_id_ctor binder) 0 public_typ in
  let rec existential_carrier ctx kopts typ =
    let typ = expand_synonyms_for_dependent_type ctx typ in
    match typ with
    | Typ_aux (Typ_exist (outer_kopts, nc, inner), l) ->
        let env = List.fold_left (fun env kopt -> Env.add_typ_var l kopt env) ctx.env outer_kopts in
        let env = try Env.add_constraint nc env with Type_internal.Type_error _ -> env in
        existential_carrier (context_with_env ctx env) (kopts @ relevant_existential_kopts outer_kopts inner) inner
    | _ -> (ctx, kopts, typ)
  in
  let carrier_ctx, witness_kopts, carrier_typ = existential_carrier ctx [] public_typ in
  let add_carrier_witness_docs ctx candidate_typ =
    try
      let goals = KidSet.of_list (List.map kopt_kid witness_kopts) in
      let unifiers = Type_check.unify (typ_loc candidate_typ) carrier_ctx.env goals carrier_typ candidate_typ in
      let () =
        if debug_dependent_representation then
          Printf.eprintf
            "lean-dependent-binder: binder=%s public=%s carrier=%s candidate=%s witnesses={%s} unifiers={%s}\n%!"
            (string_of_id binder) (string_of_typ public_typ) (string_of_typ carrier_typ) (string_of_typ candidate_typ)
            (String.concat "," (List.map (fun kopt -> string_of_kid (kopt_kid kopt)) witness_kopts))
            (String.concat ","
               (List.map
                  (fun (kid, arg) -> string_of_kid kid ^ "=" ^ string_of_typ_arg arg)
                  (KBindings.bindings unifiers)
               )
            )
      in
      List.mapi (fun index kopt -> (index, kopt_kid kopt)) witness_kopts
      |> List.fold_left
           (fun ctx (index, witness) ->
             match KBindings.find_opt witness unifiers with
             | Some (A_aux (A_nexp (Nexp_aux (Nexp_var raw_kid, _)), _)) ->
                 let witness_doc =
                   string (Printf.sprintf "%s_dependentWitness%i" (fix_id (string_of_id binder)) index)
                 in
                 { ctx with kid_docs = KBindings.add raw_kid witness_doc ctx.kid_docs }
             | _ -> ctx
           )
           ctx
    with _ -> ctx
  in
  let ctx = add_carrier_witness_docs ctx raw_typ in
  let ctx = add_carrier_witness_docs ctx pattern_typ in
  (ctx, bindings)

let doc_funcl_init global (FCL_aux (FCL_funcl (id, pexp), annot)) =
  let env = env_of_tannot (snd annot) in
  let tq, typ = Env.get_val_spec_orig id env in
  let arg_typs, ret_typ, _ =
    match typ with
    | Typ_aux (Typ_fn (arg_typs, ret_typ), _) -> (arg_typs, ret_typ, no_effect)
    | _ -> failwith ("Function " ^ string_of_id id ^ " does not have function type")
  in
  let pat, _, exp, _ = destruct_pexp pexp in
  let pats, fixup_binders = untuple_args_pat arg_typs pat in
  let ctx = context_init env global in
  let dependent_result = prop_dependent_result_for_id ctx id in
  let public_arg_typs, public_ret_typ =
    match semantic_function_type ctx id with
    | Some (semantic_arg_typs, semantic_ret_typ) ->
        let semantic_pats, _ = untuple_args_pat semantic_arg_typs pat in
        (List.map snd semantic_pats, semantic_ret_typ)
    | None -> (arg_typs, ret_typ)
  in
  let public_arg_typs = if List.length public_arg_typs = List.length pats then public_arg_typs else arg_typs in
  let lean_bound_nvars =
    List.fold_left
      (fun kids typ -> KidSet.union kids (lean_nvars_of_typ typ))
      (lean_nvars_of_typ public_ret_typ) public_arg_typs
  in
  let ctx = { ctx with lean_bound_nvars; function_bound_nvars = lean_bound_nvars } in
  let relevant_constraint_kids =
    if contains_prop_dependent_alias ctx public_ret_typ then
      close_constraint_kids tq
        (KidSet.union (dependent_tail_carrier_kids ctx exp) (dependent_record_construction_kids ctx exp))
    else KidSet.empty
  in
  prop_dependent_constraint_kids :=
    if KidSet.is_empty relevant_constraint_kids then Bindings.remove id !prop_dependent_constraint_kids
    else Bindings.add id relevant_constraint_kids !prop_dependent_constraint_kids;
  let binders : (tannot pat * id * typ * typ) list =
    pats
    |> List.mapi (fun i (pat, typ) ->
        let public_typ = List.nth public_arg_typs i in
        match pat_is_plain_binder ~suffix:(Printf.sprintf "_%i" i) env pat with
        | Some (Some id, _) -> (pat, id, typ, public_typ)
        | Some (None, _) ->
            (pat, mk_id ~loc:(pat_loc pat) (Printf.sprintf "x_%i" i), typ, public_typ)
            (* TODO fresh name or wildcard instead of x *)
        | _ ->
            ( pat,
              Id_aux (Id "TODO_ARG_PATTERN", Unknown),
              Typ_aux (Typ_id (Id_aux (Id "TODO_ARG_PATTERN", Unknown)), Unknown),
              public_typ
            )
        (*failwith "Argument pattern not translatable yet."*)
    )
  in
  let ctx, binders, fixup_binders, arg_unpacks =
    List.fold_left
      (fun (ctx, bs, fixup_binders, arg_unpacks) (pat, i, raw_typ, public_typ) ->
        let ctx, d = doc_binder ctx i public_typ in
        let () =
          if debug_dependent_representation then
            Printf.eprintf "lean-dependent-function-binder: binder=%s pattern=%s pattern-type=%s raw=%s public=%s\n%!"
              (string_of_id i) (string_of_pat pat)
              (string_of_typ (typ_of_pat pat))
              (string_of_typ raw_typ) (string_of_typ public_typ)
        in
        let preserve_prop_dependent =
          prop_dependent_alias_for_typ ctx public_typ
          || prop_dependent_record_typ public_typ
          || prop_dependent_record_typ (expand_synonyms_for_dependent_type ctx public_typ)
        in
        let ctx, witness_unpacks =
          if has_top_level_dependent_type ctx public_typ && not preserve_prop_dependent then
            dependent_binder_witnesses ctx i public_typ raw_typ (typ_of_pat pat)
          else (ctx, [])
        in
        let fixup_binders = add_function_pattern ctx fixup_binders pat i raw_typ in
        let ctx = add_path_renamings ~path:(string_of_id i) ctx pat raw_typ in
        let binder_carrier =
          if preserve_prop_dependent then doc_dependent_unpack ctx public_typ (doc_id_ctor i) else doc_id_ctor i
        in
        let ctx = add_prop_dependent_record_binder_kid_docs ctx binder_carrier raw_typ in
        let unpacked =
          if has_top_level_dependent_type ctx public_typ && not preserve_prop_dependent then
            doc_dependent_unpack ctx public_typ (doc_id_ctor i)
          else doc_id_ctor i
        in
        let unpacked =
          if has_semantic_range ctx public_typ then doc_semantic_unpack ctx public_typ unpacked else unpacked
        in
        let arg_unpacks =
          if
            (has_top_level_dependent_type ctx public_typ && not preserve_prop_dependent)
            || has_semantic_range ctx public_typ
          then arg_unpacks @ witness_unpacks @ [separate space [string "let"; doc_id_ctor i; coloneq; unpacked]]
          else arg_unpacks
        in
        let ctx =
          if has_top_level_dependent_type ctx public_typ && not preserve_prop_dependent then
            { ctx with unpacked_dependent_ids = IdSet.add i ctx.unpacked_dependent_ids }
          else if preserve_prop_dependent then
            {
              ctx with
              unpacked_dependent_ids = IdSet.remove i ctx.unpacked_dependent_ids;
              packed_dependent_types = Bindings.add i public_typ ctx.packed_dependent_types;
            }
          else ctx
        in
        (ctx, bs @ [d], fixup_binders, arg_unpacks)
      )
      (ctx, [], fixup_binders, []) binders
  in
  let typ_quant_comment = doc_typ_quant_in_comment ctx tq in
  let constraint_binders =
    if not (KidSet.is_empty relevant_constraint_kids) then
      List.mapi
        (fun index (QI_aux (item, _)) ->
          match item with
          | QI_constraint nc when constraint_relevant_to relevant_constraint_kids nc ->
              Some
                (parens
                   (separate space [string (Printf.sprintf "_sailConstraint%i" index); colon; doc_nconstraint ctx nc])
                )
          | _ -> None
        )
        tq
      |> List.filter_map Fun.id
    else if not !opt_constraint_obligations then []
    else (
      (* Sail discharges a function's constraints at every call site, so its
         body may rely on them.  Lean has to be told: without them a validity
         obligation raised inside the body -- constructing a constrained
         record, refining an index -- has no facts to work from.  They are
         autoParams, so an ordinary call site still passes nothing and the
         caller's own hypotheses discharge them.

         Only constraints whose variables the rendered signature actually
         binds can be stated; one over a variable Lean never sees would
         auto-bind a fresh implicit that no call site could determine. *)
      let env = try Env.add_typquant Unknown tq ctx.env with Type_internal.Type_error _ -> ctx.env in
      let constraint_var_available kid =
        KidSet.mem kid ctx.function_bound_nvars
        || match KBindings.find_opt kid ctx.kid_id_renames with Some (Some _) -> true | _ -> false
      in
      List.mapi
        (fun index (QI_aux (item, _)) ->
          match item with
          | QI_constraint nc when KidSet.for_all constraint_var_available (tyvars_of_constraint nc) ->
              let nc = try Env.expand_constraint_synonyms env nc with Type_internal.Type_error _ -> nc in
              Some
                (parens
                   (flow (break 1)
                      [
                        string (Printf.sprintf "_sailConstraint%i" index);
                        colon;
                        doc_nconstraint ctx nc;
                        coloneq;
                        doc_discharge_by;
                      ]
                   )
                )
          | _ -> None
        )
        tq
      |> List.filter_map Fun.id
    )
  in
  (* Use auto-implicits for type quanitifiers for now and see if this works *)
  let doc_ret_typ_orig =
    match dependent_result with
    | Some result -> doc_prop_dependent_result_type ctx result
    | None ->
        if prop_dependent_record_typ public_ret_typ then doc_dependent_shape ctx public_ret_typ
        else doc_typ ctx public_ret_typ
  in
  let is_monadic = not (Effects.function_is_pure id ctx.global.effect_info) in
  let early_return = has_early_return exp in
  let has_loop = has_loop exp in
  (* Add monad for stateful functions *)
  let doc_ret_typ = if is_monadic then string "SailM " ^^ doc_ret_typ_orig else doc_ret_typ_orig in
  let decl_val = [doc_ret_typ; coloneq] in
  (* Add do block for stateful functions *)
  let dec_val_end =
    match (is_monadic, early_return, has_loop) with
    | true, true, _ -> [string "SailME.run"; string "do"]
    | true, _, _ -> [string "do"]
    | false, false, true -> [string "Id.run"; string "do"]
    | false, true, _ -> [string "ExceptM.run"; string "do"]
    | _ -> []
  in
  let ctx =
    {
      ctx with
      in_sail_monad = is_monadic;
      in_except_monad = (if early_return then Some doc_ret_typ_orig else None);
      semantic_return = (if has_semantic_range ctx public_ret_typ then Some public_ret_typ else None);
      dependent_return = (if has_dependent_type ctx public_ret_typ then Some public_ret_typ else None);
      dependent_result;
    }
  in
  let decl_val = decl_val @ dec_val_end in
  let partiality = if IdSet.mem id !opt_partial_functions then string "partial" else empty in
  let computability = if IdSet.mem id !opt_noncomputable_functions then string "noncomputable" else empty in
  ( typ_quant_comment,
    separate space
      (remove_empties [partiality; computability; string "def"; doc_id_ctor id]
      @ binders @ constraint_binders @ [colon] @ decl_val
      ),
    ctx,
    fixup_binders,
    arg_unpacks,
    dec_val_end <> []
  )

let mapping_regex = Str.regexp "_\\(forward\\|backwards\\)\\(_matches\\)?$"

(* Mappings with string concatenation on the LHS are not translated to
executable code by sail, so we detect the pattern to replace the forward mapping
direction by a function that throws an exception. cf #260 *)
let untranslatable_mapping id exp =
  let rec exp_disc e =
    match e with
    | E_aux (E_let (_, _, e), _) -> exp_disc e
    | E_aux (E_app (_, [E_aux (E_exit _, _)]), _) -> true
    | _ -> false
  in
  let rec exp_match e =
    match e with E_aux (E_let (_, _, e), _) -> exp_match e | E_aux (E_match (e, _), _) -> exp_disc e | _ -> false
  in

  let id = string_of_id id in
  if Str.string_match mapping_regex id 0 then false else exp_match exp

let numeric_literal_is expected = function
  | E_aux (E_lit (L_aux (L_num actual, _)), _) -> Big_int.equal actual expected
  | _ -> false

let structural_fuel_parts id exp =
  let limit = mk_id "#reclimit" in
  if not (Util.starts_with ~prefix:"#rec#" (string_of_id id)) then None
  else (
    match exp with
    | E_aux (E_if (E_aux (E_app (eq, [E_aux (E_id tested, _); zero]), _), exhausted, body), _)
      when string_of_id eq = "eq_int" && Id.compare tested limit = 0 && numeric_literal_is Big_int.zero zero ->
        let predecessor = mk_id "#reclimit_pred" in
        let open Rewriter in
        let body =
          fold_exp
            {
              id_exp_alg with
              e_app =
                (fun (f, args) ->
                  match args with
                  | [E_aux (E_id tested, _); one]
                    when string_of_id f = "sub_nat"
                         && Id.compare tested limit = 0
                         && numeric_literal_is (Big_int.of_int 1) one ->
                      E_id predecessor
                  | _ -> E_app (f, args)
                );
            }
            body
        in
        Some (limit, predecessor, exhausted, body)
    | _ -> None
  )

let doc_structural_fuel_body is_monadic ctx limit predecessor exhausted body =
  let clause pattern branch =
    group (nest 2 (string "| " ^^ pattern ^^ string " =>" ^^ break 1 ^^ wrap_exp is_monadic ctx branch))
  in
  string "match " ^^ doc_id_ctor limit ^^ string " with" ^^ hardline
  ^^ clause (string "0") exhausted
  ^^ hardline
  ^^ clause (doc_id_ctor predecessor ^^ string " + 1") body

let doc_funcl_body fixup_binders arg_unpacks has_outer_do ctx (FCL_aux (FCL_funcl (id, pexp), annot)) =
  let env = env_of_tannot (snd annot) in
  let _, _, exp, _ = destruct_pexp pexp in
  (* If an argument was [x : (Int, Int)], which is transformed to [(arg0: Int) (arg1: Int)],
     this adds a let binding at the beginning of the function, of the form [let x := (arg0, arg1)] *)
  let exp = fixup_binders exp in
  let is_monadic = has_effect exp || not (Effects.function_is_pure id ctx.global.effect_info) in
  let body =
    if untranslatable_mapping id exp then string "throw Error.Exit"
    else (
      let ctx = context_with_env ctx env in
      match structural_fuel_parts id exp with
      | Some (limit, predecessor, exhausted, body) ->
          let exhausted, body =
            match ctx.dependent_return with
            | Some public_typ -> (annotate_dependent_tail public_typ exhausted, annotate_dependent_tail public_typ body)
            | None -> (exhausted, body)
          in
          doc_structural_fuel_body is_monadic ctx limit predecessor exhausted body
      | None ->
          let exp =
            match ctx.dependent_return with Some public_typ -> annotate_dependent_tail public_typ exp | None -> exp
          in
          doc_exp is_monadic ctx exp
    )
  in
  let body =
    let pack value =
      let value = match ctx.semantic_return with Some typ -> doc_semantic_pack ctx typ value | None -> value in
      value
    in
    match (ctx.semantic_return, ctx.dependent_return) with
    | None, None -> body
    | Some _, _ ->
        if has_outer_do then
          prefix 2 1 (string "let publicResult " ^^ leftarrowdo) body
          ^^ hardline ^^ string "pure "
          ^^ parens (pack (string "publicResult"))
        else pack body
    | None, Some _ -> body
  in
  separate hardline (arg_unpacks @ [body])

let doc_termination id fixup_binders arg_unpacks ctx fnpat (Rec_aux (meas, _)) =
  match meas with
  | Rec_nonrec | Rec_rec -> empty
  | Rec_measure _ when Util.starts_with ~prefix:"#rec#" (string_of_id id) ->
      hardline ^^ string "termination_by "
      ^^ doc_id_ctor (mk_id "#reclimit")
      ^^ hardline
      ^^ string "decreasing_by all_goals exact Nat.lt_succ_self _"
  | Rec_measure (pat, exp) ->
      (* TODO: actually use the pattern *)
      let term =
        doc_exp false ctx
          (fixup_binders
             (E_aux
                ( E_let (pat, Rewrites.pat_to_exp (env_of_pat fnpat) fnpat, exp),
                  (Unknown, mk_tannot ctx.env (typ_of exp))
                )
             )
          )
      in
      let term = separate hardline (arg_unpacks @ [term]) in
      let term_by =
        string "termination_by "
        ^^ if typ_is_lean_nat ctx.env (typ_of exp) then parens term else parens term ^^ string ".toNat"
      in
      hardline ^^ term_by ^^ hardline ^^ string "decreasing_by simp_wf <;> omega"

let pat_of_funcl (FCL_aux (FCL_funcl (_, funcl), _)) =
  match funcl with Pat_aux (Pat_exp (pat, _), _) -> pat | Pat_aux (Pat_when (pat, _, _), _) -> pat

let doc_funcl ctx meas funcl =
  let comment, signature, ctx, fixup_binders, arg_unpacks, has_outer_do = doc_funcl_init ctx.global funcl in
  let (FCL_aux (FCL_funcl (id, _), _)) = funcl in
  let fnpat = pat_of_funcl funcl in
  let termination = doc_termination id fixup_binders arg_unpacks ctx fnpat meas in
  comment
  ^^ nest 2 (signature ^^ hardline ^^ doc_funcl_body fixup_binders arg_unpacks has_outer_do ctx funcl)
  ^^ termination

let string_of_pexp p =
  let pat, guard, exp, _ = destruct_pexp p in
  let guard_str = match guard with None -> "" | Some guard -> " if " ^ string_of_exp guard in
  "| " ^ string_of_pat pat ^ guard_str ^ " -> " ^ string_of_exp exp ^ "\n"

let doc_fundef ctx (FD_aux (FD_function (meas, typa, fcls), fannot) as full_fundef) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | [funcl] -> doc_funcl ctx meas funcl
  | funcls ->
      failwith
        (List.fold_left
           (fun acc (FCL_aux (FCL_funcl (id, pexp), annot)) -> acc ^ string_of_pexp pexp)
           "FD_function with more than one clause :\n" funcls
        )

let doc_type_union ctx (Tu_aux (Tu_ty_id (ty, i), _)) =
  nest 2 (flow space [pipe; doc_id_ctor i; parens (flow space [underscore; colon; doc_typ ctx ty])])

let string_of_type_def_con (TD_aux (td, _)) =
  match td with
  | TD_abbrev _ -> "TD_abbrev"
  | TD_record _ -> "TD_record"
  | TD_variant _ -> "TD_variant"
  | TD_abstract _ -> "TD_abstract"
  | TD_bitfield _ -> "TD_bitfield"
  | TD_enum _ -> "TD_enum"

let prop_dependent_record_validity ctx id tq _fields =
  let witness_paths = prop_dependent_record_declaration_witness_paths ctx IdSet.empty id in
  let kid_docs = KBindings.map (doc_field_path (string "fields")) witness_paths in
  let quantified_kids = quantified_int_kids tq in
  List.iter
    (fun kid ->
      if not (KBindings.mem kid kid_docs) then
        failwith
          (Printf.sprintf "Lean proof-refined record %s cannot recover numeric index %s from a singleton-valued field"
             (string_of_id id) (string_of_kid kid)
          )
    )
    quantified_kids;
  let valid_ctx = { ctx with kid_docs } in
  let constraints =
    List.filter_map
      (fun (QI_aux (item, _)) -> match item with QI_constraint nc -> Some (doc_nconstraint valid_ctx nc) | _ -> None)
      tq
  in
  match constraints with
  | [] -> string "True"
  | constraint_ :: constraints ->
      List.fold_left
        (fun combined constraint_ -> flow (break 1) [combined; string "∧"; constraint_])
        constraint_ constraints

let prop_dependent_record_index_equalities ctx id tq =
  let witness_paths = prop_dependent_record_declaration_witness_paths ctx IdSet.empty id in
  List.map
    (fun kid ->
      flow (break 1) [doc_field_path (string "fields") (KBindings.find kid witness_paths); string "="; doc_kid ctx kid]
    )
    (quantified_int_kids tq)

let prop_dependent_alias_validity ctx alias =
  match prop_dependent_alias_parts ctx alias with
  | Some (record, nc, inner) ->
      let witness_paths = prop_dependent_record_witness_paths ctx inner in
      let kid_docs = KBindings.map (doc_field_path (string "fields")) witness_paths in
      let valid_ctx = { ctx with kid_docs } in
      flow (break 1)
        [
          parens (separate space [doc_id_ctor record ^^ string ".Valid"; string "fields"]);
          string "∧";
          doc_nconstraint valid_ctx nc;
        ]
  | None -> failwith ("No proof-refined carrier and existential constraint found for " ^ string_of_id alias)

let doc_prop_dependent_result_declaration ctx result =
  let (Typ_aux (_, l)) = result.result_typ in
  let env = try Env.add_typquant l result.result_quant ctx.env with Type_internal.Type_error _ -> ctx.env in
  let env = List.fold_left (fun env kopt -> Env.add_typ_var l kopt env) env result.result_kopts in
  let env = try Env.add_constraint result.result_constraint env with Type_internal.Type_error _ -> env in
  let declaration_ctx = context_with_env ctx env in
  let carrier_doc = doc_prop_dependent_result_carrier_shape declaration_ctx result.result_carrier in
  let witness_docs = prop_dependent_carrier_witness_docs declaration_ctx (string "value") result.result_carrier in
  let parameter_docs =
    List.map
      (fun (KOpt_aux (KOpt_kind (kind, kid), _)) ->
        parens (separate space [doc_kid declaration_ctx kid; colon; doc_existential_kind declaration_ctx kid kind])
      )
      result.result_params
  in
  let kid_docs =
    List.fold_left
      (fun docs (KOpt_aux (KOpt_kind (_, kid), _)) -> KBindings.add kid (doc_kid declaration_ctx kid) docs)
      witness_docs result.result_params
  in
  let valid_ctx = { declaration_ctx with kid_docs } in
  let validity =
    let component_validities =
      doc_prop_dependent_result_carrier_validities valid_ctx (string "value") result.result_carrier
    in
    flow (break 1)
      (List.concat_map (fun validity -> [validity; string "∧"]) component_validities
      @ [doc_nconstraint valid_ctx result.result_constraint]
      )
  in
  let name = string result.result_name in
  let valid_head =
    separate space
      ([string "def"; string "Valid"]
      @ parameter_docs
      @ [parens (string "value : " ^^ carrier_doc); colon; string "Prop :="]
      )
  in
  let valid_application =
    separate space
      ([name ^^ string ".Valid"]
      @ List.map (fun (KOpt_aux (KOpt_kind (_, kid), _)) -> doc_kid declaration_ctx kid) result.result_params
      @ [string "value"]
      )
  in
  let abbrev_head = separate space ([string "abbrev"; name] @ parameter_docs) in
  string "namespace " ^^ name ^^ hardline ^^ valid_head ^^ hardline ^^ nest 2 validity ^^ hardline ^^ string "end "
  ^^ name ^^ hardline ^^ abbrev_head ^^ string " := { value : " ^^ carrier_doc ^^ string " // " ^^ valid_application
  ^^ string " }" ^^ hardline

let rec prop_dependent_record_default ctx seen record =
  if IdSet.mem record seen then string "default"
  else (
    match
      ( Bindings.find_opt record ctx.global.semantic_types.record_quants,
        Bindings.find_opt record ctx.global.semantic_types.record_fields
      )
    with
    | Some quant, Some fields ->
        let field_env = Env.add_typquant Unknown quant ctx.env in
        let seen = IdSet.add record seen in
        let field_default field typ =
          let value =
            match singleton_kid_of_field field_env typ with
            | Some _ -> string "0"
            | None -> (
                let typ = try Env.expand_synonyms field_env typ with Type_internal.Type_error _ -> typ in
                match typ with
                | (Typ_aux (Typ_id nested, _) | Typ_aux (Typ_app (nested, _), _)) when prop_dependent_record nested ->
                    prop_dependent_record_default ctx seen nested
                | _ -> string "default"
              )
          in
          separate space [doc_id_ctor field; coloneq; value]
        in
        braces
          (space
          ^^ separate comma_sp (List.map (fun (field, typ) -> field_default field typ) (Bindings.bindings fields))
          ^^ space
          )
    | _ -> string "default"
  )

let prop_dependent_alias_default_proof ctx alias record =
  let alias_constraint_ids =
    match prop_dependent_alias_parts ctx alias with
    | Some (_, constraint_, _) -> constraint_application_ids constraint_
    | None -> IdSet.empty
  in
  let record_constraint_ids =
    match Bindings.find_opt record ctx.global.semantic_types.record_quants with
    | Some quant -> typquant_constraint_application_ids quant
    | None -> IdSet.empty
  in
  let unfold =
    [doc_id_ctor alias ^^ string ".Valid"; doc_id_ctor record ^^ string ".Valid"]
    @ List.map doc_id_ctor (IdSet.elements (IdSet.union alias_constraint_ids record_constraint_ids))
  in
  string "by" ^^ nest 2 (hardline ^^ string "simp [" ^^ separate comma_sp unfold ^^ string "] <;> first | omega | grind")

let prop_dependent_alias_has_parameters ctx alias =
  match Bindings.find_opt alias ctx.global.semantic_types.alias_quants with
  | Some quant -> quantified_int_kids quant <> []
  | None -> false

let rec typ_blocks_derived_inhabited ctx seen (Typ_aux (typ, _) as full_typ) =
  match typ with
  | (Typ_id id | Typ_app (id, _)) when prop_dependent_alias id -> prop_dependent_alias_has_parameters ctx id
  | (Typ_id id | Typ_app (id, _)) when not (IdSet.mem id seen) -> (
      let seen = IdSet.add id seen in
      match Bindings.find_opt id ctx.global.semantic_types.record_fields with
      | Some fields -> Bindings.exists (fun _ typ -> typ_blocks_derived_inhabited ctx seen typ) fields
      | None -> (
          match Bindings.find_opt id ctx.global.semantic_types.aliases with
          | Some typ -> typ_blocks_derived_inhabited ctx seen typ
          | None -> (
              match full_typ with
              | Typ_aux (Typ_app (_, args), _) ->
                  List.exists
                    (fun (A_aux (arg, _)) ->
                      match arg with A_typ typ -> typ_blocks_derived_inhabited ctx seen typ | _ -> false
                    )
                    args
              | _ -> false
            )
        )
    )
  | Typ_tuple typs -> List.exists (typ_blocks_derived_inhabited ctx seen) typs
  | Typ_exist (_, _, typ) -> typ_blocks_derived_inhabited ctx seen typ
  | Typ_fn (args, ret) -> List.exists (typ_blocks_derived_inhabited ctx seen) (ret :: args)
  | Typ_id _ | Typ_app _ | Typ_var _ | Typ_bidir _ | Typ_internal_unknown -> false

(* Fields the Lean structure does not store, emitted instead as projections of
   the record's own index parameters.  [value.field] then reduces to the index,
   so anything Sail knows about the field -- a branch test, a call argument, an
   existential witness -- is directly a fact about the type.  They are simp
   lemmas so the tactics that discharge index refinements and validity
   obligations can see through them. *)
let doc_record_index_projections ctx id tq fields =
  let implicit_binders = doc_typ_quant_relevant ctx tq |> List.map braces in
  let applied =
    match doc_typ_quant_only_vars ctx tq with
    | [] -> doc_id_ctor id
    | args -> parens (flow space (doc_id_ctor id :: args))
  in
  List.filter_map
    (fun ((field, typ), _) ->
      match record_index_projection_nexp ctx id tq typ with
      | None -> None
      | Some nexp ->
          Some
            (nest 2
               (flow (break 1)
                  ([string "@[simp] def"; doc_id_ctor id ^^ dot ^^ doc_id_ctor field]
                  @ implicit_binders
                  @ [parens (separate space [underscore; colon; applied]); colon; doc_typ ctx typ; coloneq]
                  )
               ^^ hardline ^^ doc_nexp ctx nexp
               )
            )
    )
    fields

(* Sail attaches a constraint to a struct declaration, and it is that
   constraint -- not the field types -- that rules out the index combinations
   the specification forbids.  Dropping it makes the Lean type strictly weaker
   than the Sail one, so it becomes a proof field over the index parameters.
   The obligation is stated expanded, because the Bool type synonyms it is
   written with are opaque to the arithmetic tactics. *)
let record_validity_constraint ctx tq =
  let constraints = List.filter_map (function QI_aux (QI_constraint nc, _) -> Some nc | _ -> None) tq in
  match constraints with
  | [] -> None
  | first :: rest ->
      let nc = List.fold_left nc_and first rest in
      let env = try Env.add_typquant Unknown tq ctx.env with Type_internal.Type_error _ -> ctx.env in
      Some (try Env.expand_constraint_synonyms env nc with Type_internal.Type_error _ -> nc)

let record_validity_field_name = "sailValid"

let doc_record_validity_field ctx tq =
  if not !opt_constraint_obligations then None
  else (
    match record_validity_constraint ctx tq with
    | None -> None
    | Some nc ->
        Some
          (flow (break 1) [string record_validity_field_name; colon; doc_nconstraint ctx nc; coloneq; doc_discharge_by])
  )

let record_stored_fields ctx id tq fields =
  List.filter (fun ((_, typ), _) -> Option.is_none (record_index_projection_nexp ctx id tq typ)) fields

(* [structure C where] followed directly by [deriving] is how Lean spells a
   structure with no stored fields, which is what a record whose fields are all
   singleton indices becomes. *)
let doc_structure_fields fields_doc = if fields_doc = [] then empty else hardline ^^ separate hardline fields_doc

let doc_appended_projections projections =
  if projections = [] then empty else hardline ^^ hardline ^^ separate hardline projections

(* A record carrying a validity proof cannot derive [BEq], [Repr] or
   [Inhabited]: the proof field is a [Prop].  Equality and printing ignore it,
   which proof irrelevance justifies.  Inhabitation is only available where the
   constraint actually holds, so the instance is stated at the index defaults
   rather than for every index -- an index combination the specification
   forbids must not be inhabited, which is the point of carrying the proof. *)
let doc_record_validity_instances ctx id tq stored derive_inhabited =
  let implicit_binders = doc_typ_quant_relevant ctx tq |> List.map braces in
  let applied =
    match doc_typ_quant_only_vars ctx tq with
    | [] -> doc_id_ctor id
    | args -> parens (flow space (doc_id_ctor id :: args))
  in
  (* A field whose type is one of the record's type parameters needs that
     parameter's own instance, exactly as `deriving` would have required. *)
  let type_param_instances klass =
    List.filter_map
      (function
        | QI_aux (QI_id (KOpt_aux (KOpt_kind (K_aux (K_type, _), kid), _)), _) ->
            Some (brackets (flow space [string klass; doc_kid ctx kid]))
        | _ -> None
        )
      tq
  in
  let instance_head binders klass typ =
    flow (break 1) ([string "instance"] @ binders @ [colon; string klass; typ; coloneq])
  in
  let field_names = List.map (fun ((field, _), _) -> doc_id_ctor field) stored in
  let beq_body =
    match field_names with
    | [] -> string "⟨fun _ _ => true⟩"
    | names ->
        string "⟨fun x y => "
        ^^ separate (string " && ") (List.map (fun n -> string "x." ^^ n ^^ string " == y." ^^ n) names)
        ^^ string "⟩"
  in
  let all_int_indices =
    List.for_all
      (function
        | QI_aux (QI_id (KOpt_aux (KOpt_kind (K_aux (K_int, _), _), _)), _) | QI_aux (QI_constraint _, _) -> true
        | _ -> false
        )
      tq
  in
  let zero_indices = List.map (fun _ -> string "0") (doc_typ_quant_only_vars ctx tq) in
  let default_applied =
    match zero_indices with [] -> doc_id_ctor id | args -> parens (flow space (doc_id_ctor id :: args))
  in
  let default_literal =
    match field_names with
    | [] -> string "{ }"
    | names -> braces (space ^^ separate comma_sp (List.map (fun n -> n ^^ string " := default") names) ^^ space)
  in
  let instances =
    [
      nest 2 (instance_head (implicit_binders @ type_param_instances "BEq") "BEq" applied ^^ hardline ^^ beq_body);
      nest 2
        (instance_head implicit_binders "Repr" applied
        ^^ hardline
        ^^ string "⟨fun _ _ => Std.Format.text \""
        ^^ doc_id_ctor id ^^ string "\"⟩"
        );
    ]
    @
    if derive_inhabited && all_int_indices then
      [nest 2 (instance_head [] "Inhabited" default_applied ^^ hardline ^^ string "⟨" ^^ default_literal ^^ string "⟩")]
    else []
  in
  hardline ^^ hardline ^^ separate hardline instances

let doc_typdef ctx (TD_aux (td, tannot) as full_typdef) =
  let ctx =
    match td with
    | TD_record (_, tq, _, _) | TD_abbrev (_, tq, _) | TD_variant (_, tq, _, _) ->
        context_with_env ctx (Env.add_typquant Unknown tq ctx.env)
    | _ -> ctx
  in
  match td with
  | TD_enum (id, members, _) ->
      let ids = List.map fst members in
      let ids = List.map doc_id_ctor ids in
      let ids = List.map (fun i -> space ^^ pipe ^^ space ^^ i) ids in
      let derivers = if List.length ids == 0 then [string "Repr"] else [string "Inhabited"; string "Repr"] in
      let derivers = if IdSet.mem id !non_beq_types then derivers else string "BEq" :: derivers in
      let enums_doc = concat ids in
      let _ = opens := IdSet.add id !opens in
      let id = doc_id_ctor id in
      nest 2
        (flow (break 1) [string "inductive"; id; string "where"]
        ^^ enums_doc ^^ hardline ^^ string "deriving" ^^ space ^^ separate comma_sp derivers ^^ hardline
        ^^ string "open" ^^ space ^^ id
        )
  | TD_record (id, tq, fields, _) when prop_dependent_record id ->
      let validity = prop_dependent_record_validity ctx id tq fields in
      let indexed_vars = doc_typ_quant_relevant ctx tq |> List.map parens in
      let indexed_args = doc_typ_quant_only_vars ctx tq in
      let indexed_implicit_vars = doc_typ_quant_relevant ctx tq |> List.map braces in
      let indexed_equalities = prop_dependent_record_index_equalities ctx id tq in
      let fields_doc = doc_structure_fields (List.map (doc_typ_id ctx) (record_stored_fields ctx id tq fields)) in
      let projections = doc_record_index_projections ctx id tq fields in
      let derivers = [string "Inhabited"; string "Repr"] in
      let derivers = if IdSet.mem id !non_beq_types then derivers else string "BEq" :: derivers in
      let id_doc = doc_id_ctor id in
      let structure_doc =
        doc_typ_quant_in_comment ctx tq
        ^^ nest 2
             (flow (break 1) [string "structure"; id_doc; string "where"]
             ^^ fields_doc ^^ hardline ^^ string "deriving" ^^ space ^^ separate comma_sp derivers
             )
        ^^ doc_appended_projections projections
      in
      let valid_doc =
        separate hardline
          [
            string "namespace " ^^ id_doc;
            nest 2
              (separate space
                 [
                   string "def Valid";
                   parens (separate space [string "fields"; colon; id_doc]);
                   colon;
                   string "Prop";
                   coloneq;
                 ]
              ^^ hardline ^^ validity
              );
            nest 2
              (separate space
                 [string "abbrev Refined"; coloneq; string "{ fields :"; id_doc; string "// Valid fields }"]
              );
            nest 2
              (flow (break 1)
                 ([string "def Indexed.Valid"]
                 @ indexed_vars
                 @ [parens (separate space [string "fields"; colon; id_doc]); colon; string "Prop"; coloneq]
                 )
              ^^ hardline
              ^^ flow (break 1)
                   (parens (separate space [doc_id_ctor id ^^ string ".Valid"; string "fields"])
                   :: List.concat_map (fun equality -> [string "∧"; equality]) indexed_equalities
                   )
              );
            nest 2
              (flow (break 1)
                 ([string "abbrev Indexed"]
                 @ indexed_vars
                 @ [
                     coloneq;
                     string "{ fields :";
                     id_doc;
                     string "//";
                     parens (flow space ((string "Indexed.Valid" :: indexed_args) @ [string "fields"]));
                     string "}";
                   ]
                 )
              );
            nest 2
              (flow (break 1)
                 ([string "theorem Indexed.toRefined_valid"]
                 @ indexed_implicit_vars
                 @ [
                     parens (flow space ([string "value"; colon; string "Indexed"] @ indexed_args));
                     colon;
                     flow space [id_doc ^^ string ".Valid"; parens (string "value.val")];
                     coloneq;
                   ]
                 )
              ^^ hardline
              ^^ if indexed_equalities = [] then string "value.property" else string "value.property.1"
              );
            nest 2
              (flow (break 1)
                 ([string "def Indexed.toRefined"]
                 @ indexed_implicit_vars
                 @ [
                     parens (flow space ([string "value"; colon; string "Indexed"] @ indexed_args));
                     colon;
                     string "Refined";
                     coloneq;
                   ]
                 )
              ^^ hardline
              ^^ flow space [string "⟨value.val,"; string "Indexed.toRefined_valid value⟩"]
              );
            string "end " ^^ id_doc;
          ]
      in
      structure_doc ^^ hardline ^^ hardline ^^ valid_doc
  | TD_record (id, tq, fields, _) ->
      let stored = record_stored_fields ctx id tq fields in
      let projections = doc_record_index_projections ctx id tq fields in
      let validity = doc_record_validity_field ctx tq in
      let derive_inhabited =
        not (List.exists (fun ((_, typ), _) -> typ_blocks_derived_inhabited ctx IdSet.empty typ) stored)
      in
      let fields_doc = doc_structure_fields (List.map (doc_typ_id ctx) stored @ Option.to_list validity) in
      let rectyp = doc_typ_quant_relevant ctx tq in
      let rectyp = List.map (fun d -> parens d) rectyp |> separate space in
      let derivers = if derive_inhabited then [string "Inhabited"; string "Repr"] else [string "Repr"] in
      let derivers = if IdSet.mem id !non_beq_types then derivers else string "BEq" :: derivers in
      let deriving_doc =
        if Option.is_some validity then empty else hardline ^^ string "deriving" ^^ space ^^ separate comma_sp derivers
      in
      (* A structure whose only field is the validity proof would land in
         [Prop]; the model needs it to carry data-free runtime values, so the
         sort is stated. *)
      let sort_doc = if Option.is_some validity then string ": Type" else empty in
      doc_typ_quant_in_comment ctx tq
      ^^ nest 2
           (flow (break 1) (remove_empties [string "structure"; doc_id_ctor id; rectyp; sort_doc; string "where"])
           ^^ fields_doc ^^ deriving_doc
           )
      ^^ (if Option.is_some validity then doc_record_validity_instances ctx id tq stored derive_inhabited else empty)
      ^^ doc_appended_projections projections
  | TD_abbrev
      ( id,
        [],
        A_aux
          ( A_typ (Typ_aux (Typ_app (Id_aux (Id "range", _), [A_aux (A_nexp low, _); A_aux (A_nexp high, _)]), _) as t),
            _
          )
      )
    when !opt_semantic_range_types ->
      let id_doc = doc_id_ctor id in
      let value = string "x.value" in
      let structure_doc =
        nest 2
          (separate space [string "structure"; id_doc; string "where"]
          ^^ hardline
          ^^ separate space [string "value"; colon; doc_typ ctx t]
          ^^ hardline ^^ string "deriving Inhabited, BEq, Repr"
          )
      in
      let valid_doc =
        separate hardline
          [
            string "namespace " ^^ id_doc;
            nest 2
              (separate space
                 [
                   string "def Valid"; parens (separate space [string "x"; colon; id_doc]); colon; string "Prop"; coloneq;
                 ]
              ^^ hardline
              ^^ separate space [doc_nexp ctx low; string "≤"; value; string "∧"; value; string "≤"; doc_nexp ctx high]
              );
            string "end " ^^ id_doc;
          ]
      in
      structure_doc ^^ hardline ^^ hardline ^^ valid_doc
  | TD_abbrev (id, tq, A_aux (A_typ _, _)) when prop_dependent_alias id -> (
      match prop_dependent_record_for_alias id with
      | Some record ->
          let vars = doc_typ_quant_relevant ctx tq |> List.map parens |> separate space in
          let var_args = doc_typ_quant_only_vars ctx tq in
          let carrier = doc_id_ctor record in
          let alias = doc_id_ctor id in
          let alias_typ = mk_id_typ id in
          let applied_alias = match var_args with [] -> alias | _ -> parens (separate space (alias :: var_args)) in
          let valid_doc =
            nest 2
              (flow (break 1)
                 (remove_empties
                    [
                      string "def" ^^ space ^^ alias ^^ string ".Valid";
                      vars;
                      parens (separate space [string "fields"; colon; carrier]);
                      colon;
                      string "Prop";
                      coloneq;
                    ]
                 )
              ^^ hardline ^^ prop_dependent_alias_validity ctx id
              )
          in
          let abbreviation =
            nest 2
              (flow (break 1)
                 (remove_empties
                    [
                      string "abbrev";
                      alias;
                      vars;
                      coloneq;
                      braces
                        (space
                        ^^ separate space
                             [
                               string "fields";
                               colon;
                               carrier;
                               string "//";
                               parens (separate space (((alias ^^ string ".Valid") :: var_args) @ [string "fields"]));
                             ]
                        ^^ space
                        );
                    ]
                 )
              )
          in
          let inhabited =
            match var_args with
            | [] ->
                hardline ^^ hardline
                ^^ nest 2
                     (separate space [string "instance"; colon; string "Inhabited"; applied_alias; coloneq]
                     ^^ hardline ^^ string "⟨⟨"
                     ^^ prop_dependent_record_default ctx IdSet.empty record
                     ^^ string ", "
                     ^^ prop_dependent_alias_default_proof ctx id record
                     ^^ string "⟩⟩"
                     )
            | _ -> empty
          in
          valid_doc ^^ hardline ^^ hardline ^^ abbreviation ^^ inhabited
      | None -> failwith ("No proof-refined carrier configured for " ^ string_of_id id)
    )
  | TD_abbrev (id, tq, A_aux (A_typ t, _))
    when Option.is_some (prop_dependent_record_application t)
         && List.exists (fun (QI_aux (item, _)) -> match item with QI_constraint _ -> true | _ -> false) tq ->
      let vars = doc_typ_quant_relevant ctx tq |> List.map parens |> separate space in
      nest 2
        (flow (break 1) (remove_empties [string "abbrev"; doc_id_ctor id; vars; coloneq; doc_dependent_shape ctx t]))
  | TD_abbrev (id, tq, A_aux (A_typ (Typ_aux (Typ_app (Id_aux (Id "range", _), _), _) as t), _)) ->
      let vars = doc_typ_quant_relevant ctx tq in
      let vars = List.map parens vars in
      let vars = separate space vars in
      nest 2 (flow (break 1) (remove_empties [string "abbrev"; doc_id_ctor id; vars; coloneq; doc_typ ctx t]))
  | TD_abbrev (id, tq, A_aux (A_typ t, _)) when string_of_id id = "fp_bits" ->
      string (Printf.sprintf "-- Abbreviation %s skipped" (string_of_id id)) (* FIXME *)
  | TD_abbrev (id, tq, A_aux (A_typ t, _)) ->
      let vars = doc_typ_quant_relevant ctx tq |> List.map parens in
      let vars = separate space vars in
      nest 2 (flow (break 1) (remove_empties [string "abbrev"; doc_id_ctor id; vars; coloneq; doc_typ ctx t]))
  | TD_abbrev (id, tq, A_aux (A_nexp ne, _)) ->
      let vars = doc_typ_quant_only_vars ctx tq in
      let vars = separate space vars in
      nest 2 (flow (break 1) [string "abbrev"; doc_id_ctor id; colon; string "Int"; coloneq; doc_nexp ctx ne])
  | TD_abbrev (id, tq, A_aux (A_bool nc, _)) ->
      let vars = doc_typ_quant_relevant ctx tq |> List.map parens in
      nest 2
        (flow (break 1)
           (remove_empties
              [string "def"; doc_id_ctor id; separate space vars; colon; string "Prop"; coloneq; doc_nconstraint ctx nc]
           )
        )
  | TD_variant (id, tq, ar, _) ->
      let pp_tus = concat (List.map (fun tu -> hardline ^^ doc_type_union ctx tu) ar) in
      let rectyp = doc_typ_quant_relevant ctx tq in
      let rectyp = List.map (fun d -> parens d) rectyp |> separate space in
      let _ = opens := IdSet.add id !opens in
      let derivers = [string "Repr"] in
      let derivers = if IdSet.mem id !non_beq_types then derivers else string "BEq" :: derivers in
      let derivers = if List.length ar == 0 then derivers else string "Inhabited" :: derivers in
      doc_typ_quant_in_comment ctx tq
      ^^ nest 2
           (nest 2 (flow space (remove_empties [string "inductive"; doc_id_ctor id; rectyp; string "where"]))
           ^^ pp_tus ^^ hardline ^^ string "deriving" ^^ space ^^ separate comma_sp derivers ^^ hardline
           ^^ string "open" ^^ space ^^ doc_id_ctor id
           )
  | _ -> failwith ("Type definition " ^ string_of_type_def_con full_typdef ^ " not translatable yet.")

(* Copied from the Coq PP *)
let doc_val ctx pat exp =
  let global, id, pat_typ =
    match pat with
    | P_aux (P_typ (typ, P_aux (P_id id, _)), _) -> (ctx.global, id, Some typ)
    | P_aux (P_id id, _) -> (ctx.global, id, None)
    | P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)), _) when Id.compare id (id_of_kid kid) == 0 ->
        let global = add_global_kid_id_rename ctx.global id kid in
        (global, id, None)
    | P_aux (P_typ (typ, P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)), _)), _)
      when Id.compare id (id_of_kid kid) == 0 ->
        let global = add_global_kid_id_rename ctx.global id kid in
        (global, id, Some typ)
    | P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_app (app_id, [TP_aux (TP_var kid, _)]), _)), _)
      when Id.compare app_id (mk_id "atom") == 0 && Id.compare id (id_of_kid kid) == 0 ->
        let global = add_global_kid_id_rename ctx.global id kid in
        (global, id, None)
    | P_aux
        (P_typ (typ, P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_app (app_id, [TP_aux (TP_var kid, _)]), _)), _)), _)
      when Id.compare app_id (mk_id "atom") == 0 && Id.compare id (id_of_kid kid) == 0 ->
        let global = add_global_kid_id_rename ctx.global id kid in
        (global, id, Some typ)
    | _ -> failwith ("Pattern " ^ string_of_pat_con pat ^ " " ^ string_of_pat pat ^ " not translatable yet.")
  in
  let typpp =
    match pat_typ with
    | None -> empty
    | Some typ ->
        let typ_doc = if prop_dependent_record_typ typ then doc_dependent_shape ctx typ else doc_typ ctx typ in
        space ^^ colon ^^ space ^^ typ_doc
  in
  let semantic_typ = match pat_typ with Some typ when has_semantic_range ctx typ -> Some typ | _ -> None in
  let dependent_typ = match pat_typ with Some typ when has_top_level_dependent_type ctx typ -> Some typ | _ -> None in
  let idpp = doc_id_ctor id in
  let base_pp =
    if has_effect exp then string "unwrapValue" ^^ space ^^ parens (doc_exp true ctx exp) else doc_exp false ctx exp
  in
  let base_pp = match semantic_typ with Some typ -> doc_semantic_pack ctx typ base_pp | None -> base_pp in
  let base_pp =
    match dependent_typ with
    | Some typ when exp_has_dependent_representation ctx exp ->
        let representation_typ = dependent_representation_type ctx exp in
        if dependent_types_equivalent ctx representation_typ typ then base_pp
        else doc_dependent_repack ctx representation_typ typ base_pp
    | Some typ -> doc_dependent_pack ctx typ base_pp
    | None -> base_pp
  in
  (* A constant whose Sail type is a singleton integer *is* that integer: the
     type already fixes it, exactly as for a singleton record field.  A
     reducible abbreviation of the literal keeps that definitional in Lean, so
     a test against the constant refines an index the same way a test against
     the literal does. *)
  let singleton_constant =
    let typ =
      match pat_typ with
      | Some typ -> Some typ
      | None -> (
          try Some (typ_of exp) with _ -> None
        )
    in
    match Option.map (fun typ -> try Env.expand_synonyms ctx.env typ with Type_internal.Type_error _ -> typ) typ with
    | Some
        (Typ_aux (Typ_app (Id_aux (Id ("atom" | "implicit"), _), [A_aux (A_nexp (Nexp_aux (Nexp_constant c, _)), _)]), _)
          ) ->
        Some c
    | _ -> None
  in
  let keyword, base_pp =
    match singleton_constant with
    | Some c when Option.is_none semantic_typ && Option.is_none dependent_typ -> ("abbrev", doc_big_int c)
    | _ -> ("def", base_pp)
  in
  (global, nest 2 (group (string keyword ^^ space ^^ idpp ^^ typpp ^^ space ^^ coloneq ^/^ base_pp)))

(* Sail doc comments (/*! ... */) become Lean docstrings, and a file's
   leading /*md ... */ block becomes a Lean module docstring, so extracted
   code carries the specification prose. *)

let escape_comment_close s =
  (* a literal "-/" inside a Lean comment would terminate it *)
  let buf = Buffer.create (String.length s) in
  String.iteri
    (fun i c -> if c = '/' && i > 0 && s.[i - 1] = '-' then Buffer.add_string buf " /" else Buffer.add_char buf c)
    s;
  Buffer.contents buf

let dedent_comment s =
  let leading l =
    if String.trim l = "" then max_int
    else (
      let n = ref 0 in
      while !n < String.length l && l.[!n] = ' ' do
        incr n
      done;
      !n
    )
  in
  match String.split_on_char '\n' s with
  | [] -> s
  | first :: rest ->
      let width = List.fold_left (fun acc l -> min acc (leading l)) max_int rest in
      let strip l =
        if width <> max_int && String.length l >= width then String.sub l width (String.length l - width)
        else String.trim l
      in
      String.concat "\n" (String.trim first :: List.map strip rest)

let doc_comment_block ~is_module text =
  let opener = if is_module then "/-! " else "/-- " in
  let text = escape_comment_close (dedent_comment (String.trim text)) in
  separate hardline (List.map string (String.split_on_char '\n' (opener ^ text ^ " -/"))) ^^ hardline

let doc_docstring (dannot : 'a def_annot) =
  match dannot.doc_comment with Some dc -> doc_comment_block ~is_module:false dc.Parse_ast.contents | None -> empty

let module_doc_of_file filename =
  try
    let ic = open_in filename in
    let text = really_input_string ic (in_channel_length ic) in
    close_in ic;
    let len = String.length text in
    let is_space c = c = ' ' || c = '\t' || c = '\n' || c = '\r' in
    let rec find i =
      if i + 4 >= len then None
      else if String.sub text i 4 = "/*md" && is_space text.[i + 4] then Some (i + 4)
      else find (i + 1)
    in
    let rec scan i depth =
      if i + 1 >= len then None
      else if text.[i] = '/' && text.[i + 1] = '*' then scan (i + 2) (depth + 1)
      else if text.[i] = '*' && text.[i + 1] = '/' then if depth = 1 then Some i else scan (i + 2) (depth - 1)
      else scan (i + 1) depth
    in
    match find 0 with
    | None -> None
    | Some start -> (
        match scan start 1 with Some stop -> Some (String.trim (String.sub text start (stop - start))) | None -> None
      )
  with _ -> None

let doc_module_doc filename =
  match module_doc_of_file filename with Some md -> doc_comment_block ~is_module:true md ^^ hardline | None -> empty

let should_print_function_def def =
  match def with
  | DEF_aux (DEF_fundef fdef, dannot) -> not (Env.is_extern (id_of_fundef fdef) dannot.env "lean")
  | DEF_aux (DEF_let (pat, exp), _) -> true
  | _ -> false

let rec doc_defs_rec ctx defs types (former_funcs : document list) (docdefs : document) (pending : document) =
  (* [pending] holds the current file's module docstring; it is emitted
     just before the file's first printed definition so that chunk
     flushing (and hence import alignment) is unaffected for files that
     print nothing. *)
  match defs with
  | [] -> (types, former_funcs @ [docdefs])
  | DEF_aux (DEF_fundef fdef, dannot) :: defs' ->
      let env = dannot.env in
      let pp_f, pending =
        if Env.is_extern (id_of_fundef fdef) env "lean" then (docdefs, pending)
        else (docdefs ^^ pending ^^ doc_docstring dannot ^^ group (doc_fundef ctx fdef) ^/^ hardline, empty)
      in
      doc_defs_rec ctx defs' types former_funcs pp_f pending
  | DEF_aux (DEF_internal_mutrec fdefs, dannot) :: defs' ->
      (* The explicit-measure rewrite renames each measured member of the group
         to a #rec# helper and appends the original name as a wrapper right
         after the group. Members that carry no measure still call those
         wrappers, so the wrappers have to join the same mutual block: Lean
         resolves names across a mutual block and splits it into cliques before
         checking termination, whereas a definition placed after the block is
         simply not in scope inside it. *)
      let group_ids = List.fold_left (fun ids fdef -> IdSet.add (id_of_fundef fdef) ids) IdSet.empty fdefs in
      let is_group_measure_wrapper fdef = IdSet.mem (mk_id ("#rec#" ^ string_of_id (id_of_fundef fdef))) group_ids in
      let rec split_measure_wrappers wrappers = function
        | DEF_aux (DEF_fundef fdef, _) :: rest when is_group_measure_wrapper fdef ->
            split_measure_wrappers (wrappers @ [fdef]) rest
        | rest -> (wrappers, rest)
      in
      let wrappers, defs' = split_measure_wrappers [] defs' in
      let funs = separate_map hardline (fun fdef -> doc_fundef ctx fdef) (fdefs @ wrappers) in
      let res = string "mutual" ^^ hardline ^^ funs ^^ hardline ^^ string "end" ^^ hardline in
      doc_defs_rec ctx defs' types former_funcs (docdefs ^^ pending ^^ hardline ^^ res ^^ hardline) empty
  | DEF_aux (DEF_type tdef, _) :: defs' when List.mem (string_of_id (id_of_type_def tdef)) !opt_extern_types ->
      doc_defs_rec ctx defs' types former_funcs docdefs pending
  | DEF_aux (DEF_type tdef, dannot) :: defs' ->
      doc_defs_rec ctx defs'
        (types ^^ doc_docstring dannot ^^ group (doc_typdef ctx tdef) ^/^ hardline)
        former_funcs docdefs pending
  | DEF_aux (DEF_let (pat, exp), dannot) :: defs' ->
      let global, pp_val = doc_val ctx pat exp in
      let ctx = { ctx with global } in
      doc_defs_rec ctx defs' types former_funcs
        (docdefs ^^ pending ^^ doc_docstring dannot ^^ group pp_val ^/^ hardline)
        empty
  | DEF_aux (DEF_pragma ("include_start", Pragma_line (file, _)), _) :: defs'
  | DEF_aux (DEF_pragma ("file_start", Pragma_line (file, _)), _) :: defs'
    when Filename.check_suffix file ".sail" ->
      if docdefs = empty then doc_defs_rec ctx defs' types former_funcs docdefs (doc_module_doc file)
      else doc_defs_rec ctx defs' types (former_funcs @ [docdefs]) empty (doc_module_doc file)
  | DEF_aux (DEF_pragma ("include_end", Pragma_line (file, _)), _) :: defs'
  | DEF_aux (DEF_pragma ("file_end", Pragma_line (file, _)), _) :: defs'
    when Filename.check_suffix file ".sail" ->
      if docdefs = empty then doc_defs_rec ctx defs' types former_funcs docdefs empty
      else doc_defs_rec ctx defs' types (former_funcs @ [docdefs]) empty empty
  | d :: defs' ->
      if should_print_function_def d then failwith "this case of doc_defs_rec should be unreachable"
      else doc_defs_rec ctx defs' types former_funcs docdefs pending

let doc_defs ctx defs = doc_defs_rec ctx defs empty [] empty empty

let add_node_to_map_and_ref_set (cg : Callgraph.callgraph) (map : int Bindings.t) (acc : IntSet.t) (idx : int)
    (m : Callgraph.node) =
  let map = Bindings.add (Callgraph.node_id m) idx map in
  let deps = Callgraph.G.children cg m in
  let deps : int list = List.filter_map (fun n -> Bindings.find_opt (Callgraph.node_id n) map) deps in
  let acc = List.fold_left (fun map i -> if i < idx then IntSet.add i map else map) acc deps in
  (map, acc)

let add_def_to_map_and_ref_set cg map acc idx (d : (tannot, env) def) =
  let is = Callgraph.nodes_of_def d in
  Callgraph.NodeSet.fold (fun n (map, acc) -> add_node_to_map_and_ref_set cg map acc idx n) is (map, acc)

let rec collect_imports_rec (cg : Callgraph.callgraph) (defs : (tannot, env) def list) (map : int Bindings.t)
    (accs : IntSet.t list) (acc : IntSet.t) (idx : int) (nonempty_print : bool) : IntSet.t list =
  match defs with
  | [] -> accs @ [acc]
  | (DEF_aux ((DEF_fundef _ | DEF_internal_mutrec _ | DEF_let _ | DEF_register _), _) as d) :: defs' ->
      let map, acc = add_def_to_map_and_ref_set cg map acc idx d in
      collect_imports_rec cg defs' map accs acc idx true
  | DEF_aux (DEF_type tdef, _) :: defs' -> collect_imports_rec cg defs' map accs acc idx nonempty_print
  | DEF_aux (DEF_pragma ("include_start", Pragma_line (file, _)), _) :: defs'
  | DEF_aux (DEF_pragma ("file_start", Pragma_line (file, _)), _) :: defs'
  | DEF_aux (DEF_pragma ("include_end", Pragma_line (file, _)), _) :: defs'
  | DEF_aux (DEF_pragma ("file_end", Pragma_line (file, _)), _) :: defs'
    when Filename.check_suffix file ".sail" ->
      if not nonempty_print then collect_imports_rec cg defs' map accs acc idx nonempty_print
      else collect_imports_rec cg defs' map (accs @ [acc]) IntSet.empty (idx + 1) false
  | d :: defs' ->
      if should_print_function_def d then failwith "this case of collect_imports_rec should be unreachable"
      else collect_imports_rec cg defs' map accs acc idx nonempty_print

let collect_imports (cg : Callgraph.callgraph) (defs : (tannot, env) def list) =
  collect_imports_rec cg defs Bindings.empty [] IntSet.empty 0 false

(* Remove all imports for now, they will be printed in other files. Probably just for testing. *)
let rec remove_imports (defs : (Libsail.Type_check.tannot, Libsail.Type_check.env) def list) depth =
  match defs with
  | [] -> []
  | DEF_aux (DEF_pragma ("include_start", _), _) :: ds -> remove_imports ds (depth + 1)
  | DEF_aux (DEF_pragma ("include_end", _), _) :: ds -> remove_imports ds (depth - 1)
  | d :: ds -> if depth > 0 then remove_imports ds depth else d :: remove_imports ds depth

let add_reg_typ typ_map (typ, id, _) =
  let typ_id = State.id_of_regtyp IdSet.empty typ in
  Bindings.add typ_id (id, typ) typ_map

let register_enums registers =
  opens := IdSet.add (mk_id "Register") !opens;
  separate hardline
    [
      string "inductive Register : Type where";
      separate_map hardline (fun (_, id, _) -> string "  | " ^^ doc_id_ctor id) registers;
      string "  deriving DecidableEq, Hashable, Repr";
      string "open Register";
      empty;
    ]

let type_enum ctx registers =
  separate hardline
    [
      string "abbrev RegisterType : Register → Type";
      separate_map hardline
        (fun (typ, id, _) -> string "  | ." ^^ doc_id_ctor id ^^ string " => " ^^ doc_typ ctx typ)
        registers;
      empty;
    ]

let inhabit_enum ctx typ_map =
  separate_map hardline
    (fun (_, (id, typ)) ->
      string "instance : Inhabited (RegisterRef RegisterType "
      ^^ doc_typ ctx typ ^^ string ") where" ^^ hardline ^^ string "  default := .Reg " ^^ doc_id_ctor id
    )
    typ_map

let doc_reg_info env global registers =
  let ctx = context_init env global in
  let type_map = List.fold_left add_reg_typ Bindings.empty registers in
  let type_map = Bindings.bindings type_map in
  separate hardline [register_enums registers; type_enum ctx registers; inhabit_enum ctx type_map; empty]

let doc_monad_abbrev defs (has_registers : bool) =
  let find_exc_typ defs =
    let is_exc_typ_def = function
      | DEF_aux (DEF_type td, _) -> string_of_id (id_of_type_def td) = "exception"
      | _ -> false
    in
    if List.exists is_exc_typ_def defs then empty else string "abbrev exception := Unit\n"
  in
  let excdef = find_exc_typ defs in
  let pp_register_type = string "PreSailM RegisterType trivialChoiceSource exception" in
  let pp_register_type_e = string "PreSailME RegisterType trivialChoiceSource exception" in
  let monad = separate space [string "abbrev"; string "SailM"; coloneq; pp_register_type] in
  let monad_e =
    separate space [string "abbrev"; string "SailME"; coloneq; pp_register_type_e] ^^ hardline ^^ hardline
  in
  separate hardline (remove_empties [excdef; monad; monad_e])

let doc_dependent_pair_instances =
  string
    {|instance {α : Type} {β : α → Type} [DecidableEq α] [∀ a, BEq (β a)] :
    BEq (Sigma β) where
  beq left right :=
    if h : left.1 = right.1 then
      (h ▸ left.2) == right.2
    else
      false

instance {α : Type} {β : α → Type} [Inhabited α] [∀ a, Inhabited (β a)] :
    Inhabited (Sigma β) where
  default := ⟨default, default⟩

instance {α : Type} {β : α → Type} [Repr α] [∀ a, Repr (β a)] :
    Repr (Sigma β) where
  reprPrec value precedence :=
    reprPrec value.1 precedence ++ " => " ++ reprPrec value.2 precedence
|}

let doc_instantiations_v1 ctx env =
  let params = Monad_params.find_monad_parameters env in
  match params with
  | None -> empty
  | Some params ->
      nest 2
        (separate hardline
           [
             string "instance : Arch where";
             string "va_size := 64";
             string "pa := " ^^ doc_typ ctx params.pa_type;
             string "abort := " ^^ doc_typ ctx params.abort_type;
             string "translation := " ^^ doc_typ ctx params.translation_summary_type;
             string "trans_start := " ^^ doc_typ ctx params.trans_start_type;
             string "trans_end := " ^^ doc_typ ctx params.trans_end_type;
             string "fault := " ^^ doc_typ ctx params.fault_type;
             string "tlb_op := " ^^ doc_typ ctx params.tlbi_type;
             string "cache_op := " ^^ doc_typ ctx params.cache_op_type;
             string "barrier := " ^^ doc_typ ctx params.barrier_type;
             string "arch_ak := " ^^ doc_typ ctx params.arch_ak_type;
             string "sys_reg_id := " ^^ doc_typ ctx params.sys_reg_id_type ^^ hardline;
           ]
        )
      ^^ hardline

let doc_instantiations_v2 ctx ast =
  let type_substs, id_substs = Monad_params.find_instantiations ast in
  let ts x d = KBindings.find_opt (mk_kid x) type_substs |> Option.fold ~none:(string d) ~some:(doc_typ_app ctx) in
  let is x = Bindings.find_opt (mk_id x) id_substs |> Option.fold ~none:(string "fun _ => false") ~some:doc_id_ctor in
  let pr ?(d = "Unit") x = string (x ^ " := ") ^^ ts x d in
  let fn x = string (x ^ " := ") ^^ is x in
  string "@[reducible]" ^^ hardline
  ^^ nest 2
       (separate hardline
          [
            string "instance : Arch where";
            pr "addr_size" ~d:"64";
            pr "addr_space";
            pr "CHERI" ~d:"false";
            pr "cap_size_log" ~d:"0";
            pr "mem_acc";
            fn "mem_acc_is_explicit";
            fn "mem_acc_is_ifetch";
            fn "mem_acc_is_ttw";
            fn "mem_acc_is_relaxed";
            fn "mem_acc_is_rel_acq_rcpc";
            fn "mem_acc_is_rel_acq_rcsc";
            fn "mem_acc_is_standalone";
            fn "mem_acc_is_exclusive";
            fn "mem_acc_is_atomic_rmw";
            pr "trans_start";
            pr "trans_end";
            pr "abort";
            pr "barrier";
            pr "cache_op";
            pr "tlbi";
            pr "exn";
            pr "sys_reg_id";
          ]
       )
(*
  mem_acc_is_explicit : mem_acc -> Bool
  mem_acc_is_ifetch : mem_acc -> Bool
  mem_acc_is_ttw : mem_acc -> Bool
  mem_acc_is_relaxed : mem_acc -> Bool
  mem_acc_is_rel_acq_rcpc : mem_acc -> Bool
  mem_acc_is_rel_acq_rcsc : mem_acc -> Bool
  mem_acc_is_standalone : mem_acc -> Bool
  mem_acc_is_exclusive : mem_acc -> Bool
  mem_acc_is_atomic_rmw : mem_acc -> Bool
*)

let doc_instantiations ctx env ast =
  if Preprocess.have_symbol "CONCURRENCY_INTERFACE_V2" then doc_instantiations_v2 ctx ast
  else doc_instantiations_v1 ctx env

let main_function_stub effect_info has_registers =
  let open Effects in
  let main_function =
    if Option.fold ~none:false ~some:effectful (Bindings.find_opt (mk_id "main") effect_info.functions) then "sail_main"
    else "(λ() ↦ (pure (sail_main ()) : SailM Unit))"
  in
  let main_call = if has_registers then Printf.sprintf "(sail_model_init >=> %s)" main_function else main_function in
  nest 2
    (separate hardline
       [
         string "def main (_ : List String) : IO UInt32 := do";
         Printf.ksprintf string "main_of_sail_main ⟨default, (), default, default, default, default⟩ %s" main_call;
         empty;
       ]
    )

let populate_fun_args defs =
  let add_args args (DEF_aux (d, _)) =
    match d with
    | DEF_fundef (FD_aux (FD_function (_, _, [FCL_aux (FCL_funcl (id, Pat_aux (Pat_exp (P_aux (p, _), _), _)), _)]), _))
      -> (
        match p with
        | P_tuple ps ->
            let arg =
              List.map
                (fun (P_aux (p, _)) ->
                  match p with P_id id | P_typ (_, P_aux (P_id id, _)) -> string_of_id id | _ -> ""
                )
                ps
            in
            Bindings.add id arg args
        | P_id arg -> Bindings.add id [string_of_id arg] args
        | P_typ (_, P_aux (P_id arg, _)) -> Bindings.add id [string_of_id arg] args
        | _ -> args
      )
    | _ -> args
  in
  List.fold_left (fun args d -> add_args args d) Bindings.empty defs

let collect_semantic_types defs =
  let ranges =
    if not !opt_semantic_range_types then Bindings.empty
    else
      List.fold_left
        (fun ranges (DEF_aux (def, _)) ->
          match def with
          | DEF_type
              (TD_aux
                 ( TD_abbrev
                     ( id,
                       [],
                       A_aux
                         ( A_typ
                             (Typ_aux
                                (Typ_app (Id_aux (Id "range", _), [A_aux (A_nexp low, _); A_aux (A_nexp high, _)]), _)
                               ),
                           _
                         )
                     ),
                   _
                 )
                ) ->
              Bindings.add id { low; high } ranges
          | _ -> ranges
        )
        Bindings.empty defs
  in
  let aliases, alias_quants =
    List.fold_left
      (fun (aliases, alias_quants) (DEF_aux (def, _)) ->
        match def with
        | DEF_type (TD_aux (TD_abbrev (id, quant, A_aux (A_typ typ, _)), _)) ->
            (Bindings.add id typ aliases, Bindings.add id quant alias_quants)
        | _ -> (aliases, alias_quants)
      )
      (Bindings.empty, Bindings.empty) defs
  in
  (* Public signatures and binding types are also needed by dependent
     existential packing, independently of semantic range wrappers. *)
  let valspecs, valspec_quants, bindings, record_fields, record_quants =
    List.fold_left
      (fun (valspecs, valspec_quants, bindings, record_fields, record_quants) (DEF_aux (def, _)) ->
        match def with
        | DEF_val (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (quant, typ), _), id, _), _)) ->
            (Bindings.add id typ valspecs, Bindings.add id quant valspec_quants, bindings, record_fields, record_quants)
        | DEF_let (P_aux (P_typ (typ, P_aux (P_id id, _)), _), _) ->
            (valspecs, valspec_quants, Bindings.add id typ bindings, record_fields, record_quants)
        | DEF_type (TD_aux (TD_variant (id, _, arms, _), _)) ->
            let valspecs =
              List.fold_left
                (fun valspecs (Tu_aux (Tu_ty_id (payload, constructor), _)) ->
                  Bindings.add constructor (function_typ [payload] (mk_id_typ id)) valspecs
                )
                valspecs arms
            in
            (valspecs, valspec_quants, bindings, record_fields, record_quants)
        | DEF_type (TD_aux (TD_record (id, quant, fields, _), _)) ->
            let fields =
              List.fold_left (fun fields ((field, typ), _) -> Bindings.add field typ fields) Bindings.empty fields
            in
            ( valspecs,
              valspec_quants,
              bindings,
              Bindings.add id fields record_fields,
              Bindings.add id quant record_quants
            )
        | _ -> (valspecs, valspec_quants, bindings, record_fields, record_quants)
      )
      (Bindings.empty, Bindings.empty, Bindings.empty, Bindings.empty, Bindings.empty)
      defs
  in
  { ranges; aliases; alias_quants; valspecs; valspec_quants; bindings; record_fields; record_quants }

let infer_prop_dependent_types env semantic_types =
  let rec record_witness_paths seen record =
    if IdSet.mem record seen then None
    else (
      match
        (Bindings.find_opt record semantic_types.record_quants, Bindings.find_opt record semantic_types.record_fields)
      with
      | Some quant, Some fields ->
          let seen = IdSet.add record seen in
          let field_env = Env.add_typquant Unknown quant env in
          let witnesses =
            Bindings.fold
              (fun field typ witnesses ->
                match singleton_kid_of_field field_env typ with
                | Some kid -> KBindings.add kid [field] witnesses
                | None -> (
                    let typ = try Env.expand_synonyms field_env typ with Type_internal.Type_error _ -> typ in
                    match typ with
                    | Typ_aux (Typ_app (nested_record, args), _) -> (
                        match
                          ( Bindings.find_opt nested_record semantic_types.record_quants,
                            record_witness_paths seen nested_record
                          )
                        with
                        | Some nested_quant, Some nested_paths ->
                            let nested_kids = quantified_int_kids nested_quant in
                            let actuals = try List.combine nested_kids args with Invalid_argument _ -> [] in
                            List.fold_left
                              (fun witnesses (nested_kid, A_aux (arg, _)) ->
                                match (KBindings.find_opt nested_kid nested_paths, arg) with
                                | Some path, A_nexp (Nexp_aux (Nexp_var actual_kid, _)) ->
                                    KBindings.add actual_kid (field :: path) witnesses
                                | _ -> witnesses
                              )
                              witnesses actuals
                        | _ -> witnesses
                      )
                    | _ -> witnesses
                  )
              )
              fields KBindings.empty
          in
          let required = quantified_int_kids quant in
          if List.for_all (fun kid -> KBindings.mem kid witnesses) required then Some witnesses else None
      | _ -> None
    )
  in
  let inferred_types =
    Bindings.fold
      (fun alias typ inferred ->
        match typ with
        | Typ_aux (Typ_exist (kopts, _, (Typ_aux (Typ_app (record, args), _) as inner)), _) -> (
            match (Bindings.find_opt record semantic_types.record_quants, record_witness_paths IdSet.empty record) with
            | Some record_quant, Some record_paths ->
                let declaration_kids = quantified_int_kids record_quant in
                let actuals = try List.combine declaration_kids args with Invalid_argument _ -> [] in
                let witnesses =
                  List.fold_left
                    (fun witnesses (declaration_kid, A_aux (arg, _)) ->
                      match (KBindings.find_opt declaration_kid record_paths, arg) with
                      | Some path, A_nexp (Nexp_aux (Nexp_var actual_kid, _)) -> KBindings.add actual_kid path witnesses
                      | _ -> witnesses
                    )
                    KBindings.empty actuals
                in
                let required =
                  List.map (fun (KOpt_aux (KOpt_kind (_, kid), _)) -> kid) (relevant_existential_kopts kopts inner)
                in
                if List.for_all (fun kid -> KBindings.mem kid witnesses) required then
                  (string_of_id record, string_of_id alias) :: inferred
                else inferred
            | _ -> inferred
          )
        | _ -> inferred
      )
      semantic_types.aliases []
  in
  let inferred_records =
    Bindings.fold
      (fun record quant inferred ->
        let has_constraint =
          List.exists (fun (QI_aux (item, _)) -> match item with QI_constraint _ -> true | _ -> false) quant
        in
        let numeric_kids = quantified_int_kids quant in
        match record_witness_paths IdSet.empty record with
        | Some witnesses
          when has_constraint && numeric_kids <> []
               && List.for_all (fun kid -> KBindings.mem kid witnesses) numeric_kids ->
            string_of_id record :: inferred
        | _ -> inferred
      )
      semantic_types.record_quants []
  in
  (inferred_types, inferred_records)

let rec collect_import_files_aux defs file_stack last_namespace ret =
  match defs with
  | [] -> ret
  | DEF_aux (DEF_pragma ("include_start", Pragma_line (file, _)), _) :: ds
  | DEF_aux (DEF_pragma ("file_start", Pragma_line (file, _)), _) :: ds
    when Filename.check_suffix file ".sail" ->
      collect_import_files_aux ds (file :: file_stack) last_namespace ret
  | DEF_aux (DEF_pragma ("include_end", Pragma_line (file, _)), _) :: ds
  | DEF_aux (DEF_pragma ("file_end", Pragma_line (file, _)), _) :: ds
    when Filename.check_suffix file ".sail" -> (
      match file_stack with
      | f :: fs -> collect_import_files_aux ds fs last_namespace ret
      | _ -> failwith "should not be reachable"
    )
  | d :: ds -> (
      match file_stack with
      | f :: _ ->
          if should_print_function_def d && not (last_namespace = Some f) then
            collect_import_files_aux ds file_stack (Some f) (ret @ [f])
          else collect_import_files_aux ds file_stack last_namespace ret
      | _ -> failwith "should not be reachable"
    )

let collect_import_files defs base =
  let res = collect_import_files_aux defs [base] None [] in
  if res = [] then [base] else res

let pp_ast_lean (env : Type_check.env) effect_info ({ defs; _ } as ast : Libsail.Type_check.typed_ast) out_name_camel
    types_file imp_funcs_files funcs_file =
  dependent_pair_instances_required := false;
  prop_dependent_constraint_kids := Bindings.empty;
  let regs = State.find_registers ~expand:false defs in
  let fun_args = populate_fun_args defs in
  let semantic_types = collect_semantic_types defs in
  let inferred_prop_dependent_types, inferred_records =
    if !opt_semantic_range_types || !opt_infer_prop_dependent_types || !opt_prop_dependent_types <> [] then
      infer_prop_dependent_types env semantic_types
    else ([], [])
  in
  inferred_prop_dependent_records := List.sort_uniq String.compare inferred_records;
  opt_prop_dependent_types := List.sort_uniq compare (inferred_prop_dependent_types @ !opt_prop_dependent_types);
  let global =
    {
      effect_info;
      fun_args;
      semantic_types;
      prop_dependent_results = Bindings.empty;
      kid_id_renames = KBindings.empty;
      kid_id_renames_rev = Bindings.empty;
    }
  in
  let inference_ctx = context_init env global in
  let prop_dependent_results =
    if prop_dependent_mode_active () then
      Bindings.fold
        (fun id typ results ->
          match typ with
          | Typ_aux (Typ_fn (_, ret), _) -> (
              let tq = Option.value ~default:[] (Bindings.find_opt id semantic_types.valspec_quants) in
              match infer_prop_dependent_result inference_ctx id tq ret with
              | Some result -> Bindings.add id result results
              | None -> results
            )
          | _ -> results
        )
        semantic_types.valspecs Bindings.empty
    else Bindings.empty
  in
  let global = { global with prop_dependent_results } in
  let ctx = context_init env global in
  let inst_defs, defs = Callgraph.partition_instantiation_definitions false defs in
  let ast = { ast with defs } in
  let _, instantiation_deps = doc_defs ctx inst_defs in
  let instantiation_deps =
    match instantiation_deps with [x] -> x | _ -> failwith "expected a single block of instantiation defs"
  in
  let instantiations = doc_instantiations ctx env defs in
  let has_registers = List.length regs > 0 in
  let register_refs =
    if has_registers then doc_reg_info env global regs
    else string "abbrev Register := PEmpty\nabbrev RegisterType : Register -> Type := PEmpty.elim\n\n"
  in
  let monad = doc_monad_abbrev defs has_registers in
  let types, all_fundefss = doc_defs ctx defs in
  let prop_dependent_result_declarations =
    Bindings.fold
      (fun _ result declarations -> declarations ^^ doc_prop_dependent_result_declaration ctx result ^^ hardline)
      global.prop_dependent_results empty
  in
  let dependent_pair_instances =
    if !dependent_pair_instances_required then doc_dependent_pair_instances ^^ hardline ^^ hardline else empty
  in
  let imp_fundefss, main_fundefs =
    if imp_funcs_files = [] then ([], concat all_fundefss) else (Util.butlast all_fundefss, Util.last all_fundefss)
  in
  let main_fundefs = main_fundefs ^^ string ("end " ^ out_name_camel ^ ".Functions") ^^ hardline in
  let main_function =
    if !the_main_function_has_been_seen then (
      let stub = main_function_stub effect_info has_registers in
      [string ("open " ^ out_name_camel); string ("open " ^ out_name_camel ^ ".Functions\nopen Defs\n\n") ^^ stub]
    )
    else []
  in
  let opens = IdSet.fold (fun id doc -> string "open " ^^ doc_id_ctor id ^^ hardline ^^ doc) !opens empty in
  print types_file
    (dependent_pair_instances ^^ types ^^ prop_dependent_result_declarations ^^ register_refs ^^ monad
   ^^ instantiation_deps ^^ instantiations
    );
  let _ =
    List.map2
      (fun file defs -> print file (separate hardline (remove_empties [opens; defs])))
      imp_funcs_files imp_fundefss
  in
  print ~len:!opt_line_width funcs_file (separate hardline (remove_empties ([opens; main_fundefs] @ main_function)));
  !the_main_function_has_been_seen
