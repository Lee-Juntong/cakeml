/-
  Translation of namespaceScript.sml
  Defines a datatype for nested namespaces where names can be either
  short (e.g. foo) or long (e.g. ModuleA.InnerB.bar).
-/
import LeanTypeSound.HOL4Prelude

open HOL4

/- HOL4:
Type alist = ``: ('k # 'v) list``
-/
abbrev alist (k v : Type) := List (k × v)

/- HOL4:
Datatype:
  id = Short 'n | Long 'm id
End
-/
inductive cml_id (m n : Type) where
  | Short : n → cml_id m n
  | Long : m → cml_id m n → cml_id m n
deriving Repr, BEq, Inhabited

/- HOL4:
Definition mk_id_def:
  mk_id [] n = Short n ∧
  mk_id (mn::mns) n = Long mn (mk_id mns n)
End
-/
def mk_id {m n : Type} : List m → n → cml_id m n
  | [], x => .Short x
  | mn :: mns, x => .Long mn (mk_id mns x)

/- HOL4:
Definition id_to_n_def:
 id_to_n (Short n) = n ∧
 id_to_n (Long _ id) = id_to_n id
End
-/
def id_to_n {m n : Type} : cml_id m n → n
  | .Short x => x
  | .Long _ i => id_to_n i

/- HOL4:
Definition id_to_mods_def:
  id_to_mods (Short _) = [] ∧
  id_to_mods (Long mn id) = mn::id_to_mods id
End
-/
def id_to_mods {m n : Type} : cml_id m n → List m
  | .Short _ => []
  | .Long mn i => mn :: id_to_mods i

/- HOL4:
Datatype:
  namespace =
    Bind (('n,'v) alist) (('m,namespace) alist)
End
-/
inductive «namespace» (m n v : Type) where
  | Bind : List (n × v) → List (m × «namespace» m n v) → «namespace» m n v

/- HOL4:
Definition nsLookup_def:
  nsLookup ((Bind v m):('m,'n,'v)namespace) (Short n) =
    ALOOKUP v n ∧
  nsLookup (Bind v m) (Long mn id) =
    case ALOOKUP m mn of
    | NONE => NONE
    | SOME env => nsLookup env id
End
-/
def nsLookup {m n v : Type} [BEq n] [BEq m] :
    «namespace» m n v → cml_id m n → Option v
  | .Bind vals _, .Short x => ALOOKUP vals x
  | .Bind _ mods, .Long mn i =>
    match ALOOKUP mods mn with
    | none => none
    | some env => nsLookup env i

/- HOL4:
Definition nsLookupMod_def:
  nsLookupMod e [] = SOME e ∧
  nsLookupMod (Bind v m) (mn::path) =
  case ALOOKUP m mn of NONE => NONE | SOME env => nsLookupMod env path
End
-/
def nsLookupMod {m n v : Type} [BEq m] :
    «namespace» m n v → List m → Option («namespace» m n v)
  | e, [] => some e
  | .Bind _ mods, mn :: path =>
    match ALOOKUP mods mn with
    | none => none
    | some env => nsLookupMod env path

/- HOL4:
Definition nsEmpty_def:
  nsEmpty = Bind [] []
End
-/
def nsEmpty {m n v : Type} : «namespace» m n v := .Bind [] []

/- HOL4:
Definition nsAppend_def:
  nsAppend (Bind v1 m1) (Bind v2 m2) = Bind (v1 ++ v2) (m1 ++ m2)
End
-/
def nsAppend {m n v : Type} : «namespace» m n v → «namespace» m n v → «namespace» m n v
  | .Bind v1 m1, .Bind v2 m2 => .Bind (v1 ++ v2) (m1 ++ m2)

/- HOL4:
Definition nsLift_def:
  nsLift mn env = Bind [] [(mn,env)]
End
-/
def nsLift {m n v : Type} (mn : m) (env : «namespace» m n v) : «namespace» m n v :=
  .Bind [] [(mn, env)]

/- HOL4:
Definition alist_to_ns_def:
  alist_to_ns a = Bind a []
End
-/
def alist_to_ns {m n v : Type} (a : alist n v) : «namespace» m n v := .Bind a []

/- HOL4:
Definition nsBind_def:
  nsBind k x (Bind v m) = Bind ((k,x)::v) m
End
-/
def nsBind {m n v : Type} (k : n) (x : v) : «namespace» m n v → «namespace» m n v
  | .Bind vals mods => .Bind ((k, x) :: vals) mods

/- HOL4:
Definition nsBindList_def:
  nsBindList l e = FOLDR (λ(x,v) e. nsBind x v e) e l
End
-/
def nsBindList {m n v : Type} (l : List (n × v)) (e : «namespace» m n v) : «namespace» m n v :=
  l.foldr (fun (p : n × v) (e : «namespace» m n v) => nsBind p.1 p.2 e) e

/- HOL4:
Definition nsOptBind_def:
  nsOptBind n x env = case n of NONE => env | SOME n => nsBind n x env
End
-/
def nsOptBind {m n v : Type} (name : Option n) (x : v) (env : «namespace» m n v) :
    «namespace» m n v :=
  match name with
  | none => env
  | some n' => nsBind n' x env

/- HOL4:
Definition nsSing_def:
  nsSing n x = Bind [(n,x)] []
End
-/
def nsSing {m n v : Type} (name : n) (x : v) : «namespace» m n v := .Bind [(name, x)] []

/- HOL4:
Definition nsSub_def:
  nsSub r env1 env2 ⇔ ...
End
-/
def nsSub {m n v1 v2 : Type} [BEq m] [BEq n]
    (r : cml_id m n → v1 → v2 → Prop) (env1 : «namespace» m n v1) (env2 : «namespace» m n v2) :
    Prop :=
  (∀ id_ v1_, nsLookup env1 id_ = some v1_ →
    ∃ v2_, nsLookup env2 id_ = some v2_ ∧ r id_ v1_ v2_) ∧
  (∀ path, (nsLookupMod env2 path = (none : Option («namespace» m n v2))) →
    nsLookupMod env1 path = none)

/- HOL4:
Definition nsAll_def:
  nsAll f env ⇔ ∀id v. nsLookup env id = SOME v ⇒ f id v
End
-/
def nsAll {m n v : Type} [BEq m] [BEq n]
    (f : cml_id m n → v → Prop) (env : «namespace» m n v) : Prop :=
  ∀ id_ val_, nsLookup env id_ = some val_ → f id_ val_

/- HOL4:
Definition nsAll2_def:
  nsAll2 r env1 env2 ⇔
    nsSub r env1 env2 ∧ nsSub (λx y z. r x z y) env2 env1
End
-/
def nsAll2 {m n v1 v2 : Type} [BEq m] [BEq n]
    (r : cml_id m n → v1 → v2 → Prop) (env1 : «namespace» m n v1) (env2 : «namespace» m n v2) :
    Prop :=
  nsSub r env1 env2 ∧ nsSub (fun x y z => r x z y) env2 env1

/- HOL4:
Definition nsDom_def:
  nsDom env = {n | ... nsLookup env n = SOME v}
End
-/
def nsDom {m n v : Type} [BEq m] [BEq n] (env : «namespace» m n v) : Set (cml_id m n) :=
  fun (i : cml_id m n) => ∃ val_ : v, nsLookup env i = some val_

/- HOL4:
Definition nsMap_def:
  nsMap f (Bind v m) =
    Bind (MAP (λ(n,x). (n,f x)) v) (MAP (λ(mn,e). (mn,nsMap f e)) m)
End
-/
def nsMap {m n v w : Type} (f : v → w) : «namespace» m n v → «namespace» m n w
  | .Bind vals mods =>
    .Bind (vals.map fun (name, x) => (name, f x))
          (mods.attach.map fun ⟨(mn, e), hmem⟩ => (mn, nsMap f e))
  decreasing_by
    have h1 := List.sizeOf_lt_of_mem hmem
    simp [«namespace».Bind.sizeOf_spec] at *
    omega
