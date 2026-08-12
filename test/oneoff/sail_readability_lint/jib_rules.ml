open Libsail
open Ast
open Ast_util
open Jib

module StringSet = Set.Make (String)

let annot = (0, Parse_ast.Unknown)
let instr auxiliary = I_aux (auxiliary, annot)
let local name = Name (mk_id name, -1)
let generated ?(source = Some "tmp") number = Gen (number, 0, 0, source, None)
let bool value = V_lit (VL_bool value, CT_bool)
let unit_value = V_lit (VL_unit, CT_unit)
let id name typ = V_id (name, typ)

let rule_set instructions =
  Jib_compile.jib_readability_findings instructions
  |> List.fold_left
       (fun rules (finding : Jib_compile.jib_readability_finding) -> StringSet.add finding.rule rules)
       StringSet.empty

let require_rules expected actual =
  List.iter
    (fun rule -> if not (StringSet.mem rule actual) then failwith ("missing Jib readability rule: " ^ rule))
    expected

let reject_rules rejected actual =
  List.iter
    (fun rule -> if StringSet.mem rule actual then failwith ("unexpected Jib readability rule: " ^ rule))
    rejected

let () =
  let split = local "split" in
  let unit_local = local "unit_local" in
  let once = generated 1 in
  let dead = generated 2 in
  let unnamed = generated ~source:None 3 in
  let condition = local "condition" in
  let partial = local "partial" in
  let positive =
    [
      instr (I_decl (CT_bool, split));
      instr (I_copy (CL_id (split, CT_bool), bool true));
      instr (I_decl (CT_unit, unit_local));
      instr (I_comment "separate the unit declaration from the next rule");
      instr (I_init (CT_bool, once, Init_cval (bool true)));
      instr (I_return (id once CT_bool));
      instr (I_init (CT_bool, dead, Init_cval (bool false)));
      instr (I_goto "join");
      instr (I_label "join");
      instr (I_label "dead_label");
      instr (I_block [instr (I_comment "singleton")]);
      instr (I_if (bool true, [instr (I_comment "then")], []));
      instr (I_if (id condition CT_bool, [], []));
      instr
        (I_if
           ( id condition CT_bool,
             [instr (I_copy (CL_id (split, CT_bool), bool true))],
             [instr (I_copy (CL_id (split, CT_bool), bool true))]
           )
        );
      instr
        (I_if
           ( id condition CT_bool,
             [instr (I_copy (CL_id (split, CT_bool), bool true))],
             [instr (I_copy (CL_id (split, CT_bool), bool false))]
           )
        );
      instr
        (I_if
           (id condition CT_bool, [instr (I_return (bool true))], [instr (I_copy (CL_id (split, CT_bool), bool false))])
        );
      instr (I_decl (CT_bool, partial));
      instr
        (I_if
           ( id condition CT_bool,
             [instr (I_copy (CL_id (partial, CT_bool), bool true))],
             [instr (I_comment "falls through without an assignment")]
           )
        );
      instr (I_return (id partial CT_bool));
      instr (I_copy (CL_id (split, CT_bool), id split CT_bool));
      instr (I_init (CT_bool, unnamed, Init_cval (V_call (Bnot, [V_call (Bnot, [bool true])]))));
      instr (I_return unit_value);
    ]
  in
  let positive_rules = rule_set positive in
  require_rules
    [
      "jib-declaration-assignment-split";
      "jib-unit-plumbing";
      "jib-single-use-pure-temporary";
      "jib-dead-pure-temporary";
      "jib-redundant-bool";
      "jib-constant-conditional";
      "jib-empty-conditional";
      "jib-duplicate-branches";
      "jib-conditional-assignment";
      "jib-else-after-terminal";
      "jib-partial-branch-initialization";
      "jib-identity-copy";
      "jib-redundant-join";
      "jib-redundant-scope";
      "jib-dead-label";
      "jib-lost-source-name";
    ]
    positive_rules;

  let semantic = local "parsed_header" in
  let multi_use = generated ~source:(Some "semantic_origin") 4 in
  let rewritten = generated 5 in
  let call_result = generated 6 in
  let safely_partial = local "safely_partial" in
  let negative =
    [
      instr (I_init (CT_bool, semantic, Init_cval (bool true)));
      instr (I_init (CT_bool, multi_use, Init_cval (bool true)));
      instr (I_copy (CL_id (semantic, CT_bool), id multi_use CT_bool));
      instr (I_return (id multi_use CT_bool));
      instr (I_init (CT_bool, rewritten, Init_cval (bool true)));
      instr (I_copy (CL_id (rewritten, CT_bool), bool false));
      instr (I_funcall (CR_one (CL_id (call_result, CT_bool)), Extern CT_bool, (mk_id "observe", []), []));
      instr (I_if (id condition CT_bool, [instr (I_comment "nonempty")], []));
      instr (I_if (id condition CT_bool, [instr (I_comment "left")], [instr (I_comment "right")]));
      instr
        (I_if
           ( id condition CT_bool,
             [instr (I_copy (CL_id (semantic, CT_bool), bool true))],
             [instr (I_copy (CL_id (rewritten, CT_bool), bool false))]
           )
        );
      instr (I_if (id condition CT_bool, [instr (I_comment "continues")], [instr (I_return (bool false))]));
      instr (I_decl (CT_bool, safely_partial));
      instr
        (I_if
           ( id condition CT_bool,
             [instr (I_copy (CL_id (safely_partial, CT_bool), bool true))],
             [instr (I_return (bool false))]
           )
        );
      instr (I_return (id safely_partial CT_bool));
      instr (I_copy (CL_id (semantic, CT_bool), id multi_use CT_bool));
    ]
  in
  let negative_rules = rule_set negative in
  reject_rules
    [
      "jib-declaration-assignment-split";
      "jib-unit-plumbing";
      "jib-single-use-pure-temporary";
      "jib-dead-pure-temporary";
      "jib-redundant-bool";
      "jib-constant-conditional";
      "jib-empty-conditional";
      "jib-duplicate-branches";
      "jib-conditional-assignment";
      "jib-else-after-terminal";
      "jib-partial-branch-initialization";
      "jib-identity-copy";
      "jib-redundant-join";
      "jib-redundant-scope";
      "jib-dead-label";
      "jib-lost-source-name";
    ]
    negative_rules
