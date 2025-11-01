import Lean

open Lean Parser in

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

-- ドキュメントコメントで `namespace` を修飾しようとすると構文エラーになる
/-⋆-//--
error: <input>:1:21: expected '#guard_msgs', 'abbrev', 'add_decl_doc', 'axiom', 'binder_predicate', 'builtin_dsimproc', 'builtin_dsimproc_decl', 'builtin_grind_propagator', 'builtin_initialize', 'builtin_simproc', 'builtin_simproc_decl', 'class', 'coinductive', 'declare_command_config_elab', 'declare_config_elab', 'declare_simp_like_tactic', 'declare_syntax_cat', 'def', 'dsimproc', 'dsimproc_decl', 'elab', 'elab_rules', 'example', 'grind_propagator', 'inductive', 'infix', 'infixl', 'infixr', 'initialize', 'instance', 'macro', 'macro_rules', 'notation', 'opaque', 'postfix', 'prefix', 'recommended_spelling', 'register_builtin_option', 'register_error_explanation', 'register_label_attr', 'register_linter_set', 'register_option', 'register_simp_attr', 'register_tactic_tag', 'simproc', 'simproc_decl', 'structure', 'syntax', 'tactic_extension', 'theorem' or 'unif_hint'
-/
#guard_msgs in --#
#eval parse `command "/-- これはドキュメントコメント -/ namespace Foo"
