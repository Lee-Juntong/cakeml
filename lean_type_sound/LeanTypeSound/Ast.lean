/-
  Translation of astScript.sml
  Definition of CakeML abstract syntax (AST).
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Mlstring
import LeanTypeSound.Namespace
import LeanTypeSound.Location

open HOL4

-- Type abbreviations for names
/- HOL4: Type modN = ":mlstring" -/
abbrev modN := mlstring
/- HOL4: Type varN = ":mlstring" -/
abbrev varN := mlstring
/- HOL4: Type conN = ":mlstring" -/
abbrev conN := mlstring
/- HOL4: Type typeN = ":mlstring" -/
abbrev typeN := mlstring
/- HOL4: Type tvarN = ":mlstring" -/
abbrev tvarN := mlstring

/- HOL4:
Datatype:
  lit =
    IntLit int | Char char | StrLit mlstring | Word8 word8 | Word64 word64 | Float64 word64
End
-/
inductive lit where
  | IntLit : Int → lit
  | Char : Char → lit
  | StrLit : mlstring → lit
  | Word8 : word8 → lit
  | Word64 : word64 → lit
  | Float64 : word64 → lit
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  shift = Lsl | Lsr | Asr | Ror
End
-/
inductive shift where
  | Lsl | Lsr | Asr | Ror
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  arith = Add | Sub | Mul | Div | Mod | Neg | And | Xor | Or | Not | Abs | Sqrt | FMA
End
-/
inductive arith where
  | Add | Sub | Mul | Div | Mod | Neg | And | Xor | Or | Not | Abs | Sqrt | FMA
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  word_size = W8 | W64
End
-/
inductive word_size where
  | W8 | W64
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  thunk_mode = Evaluated | NotEvaluated
End
-/
inductive thunk_mode where
  | Evaluated | NotEvaluated
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  thunk_op = AllocThunk thunk_mode | UpdateThunk thunk_mode | ForceThunk
End
-/
inductive thunk_op where
  | AllocThunk : thunk_mode → thunk_op
  | UpdateThunk : thunk_mode → thunk_op
  | ForceThunk : thunk_op
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  opb = Lt | Gt | Leq | Geq
End
-/
inductive opb where
  | Lt | Gt | Leq | Geq
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  test = Equal | Compare opb | AltCompare opb
End
-/
inductive test where
  | Equal : test
  | Compare : opb → test
  | AltCompare : opb → test
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  prim_type = BoolT | IntT | CharT | StrT | WordT word_size | Float64T
End
-/
inductive prim_type where
  | BoolT | IntT | CharT | StrT
  | WordT : word_size → prim_type
  | Float64T
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  op = Arith arith prim_type | FromTo prim_type prim_type | Shift word_size shift num
     | Equality | Test test prim_type | Opapp | Opassign | Opref | Opderef
     | Aw8alloc | Aw8sub | Aw8length | Aw8update
     | CopyStrStr | CopyStrAw8 | CopyAw8Str | CopyAw8Aw8 | XorAw8Str_unsafe
     | Implode | Explode | Strsub | Strlen | Strcat
     | VfromList | Vsub | Vlength
     | Aalloc | AallocEmpty | AallocFixed | Asub | Alength | Aupdate
     | Vsub_unsafe | Asub_unsafe | Aupdate_unsafe | Aw8sub_unsafe | Aw8update_unsafe
     | ThunkOp thunk_op | ListAppend | ConfigGC | FFI mlstring | Eval | Env_id
End
-/
inductive op where
  | Arith : arith → prim_type → op
  | FromTo : prim_type → prim_type → op
  | Shift : word_size → shift → Nat → op
  | Equality : op
  | Test : test → prim_type → op
  | Opapp : op
  | Opassign : op
  | Opref : op
  | Opderef : op
  | Aw8alloc : op
  | Aw8sub : op
  | Aw8length : op
  | Aw8update : op
  | CopyStrStr : op
  | CopyStrAw8 : op
  | CopyAw8Str : op
  | CopyAw8Aw8 : op
  | XorAw8Str_unsafe : op
  | Implode : op
  | Explode : op
  | Strsub : op
  | Strlen : op
  | Strcat : op
  | VfromList : op
  | Vsub : op
  | Vlength : op
  | Aalloc : op
  | AallocEmpty : op
  | AallocFixed : op
  | Asub : op
  | Alength : op
  | Aupdate : op
  | Vsub_unsafe : op
  | Asub_unsafe : op
  | Aupdate_unsafe : op
  | Aw8sub_unsafe : op
  | Aw8update_unsafe : op
  | ThunkOp : thunk_op → op
  | ListAppend : op
  | ConfigGC : op
  | FFI : mlstring → op
  | Eval : op
  | Env_id : op
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  op_class = EvalOp | FunApp | Force | Simple
End
-/
inductive op_class where
  | EvalOp | FunApp | Force | Simple
deriving Repr, BEq, Inhabited

/- HOL4:
Definition getOpClass_def[simp]:
  getOpClass op = case op of Opapp => FunApp | Eval => EvalOp
    | ThunkOp t => (if t = ForceThunk then Force else Simple) | _ => Simple
End
-/
def getOpClass : op → op_class
  | .Opapp => .FunApp
  | .Eval => .EvalOp
  | .ThunkOp t => if t == .ForceThunk then .Force else .Simple
  | _ => .Simple

/- HOL4:
Datatype:
  ast_t = Atvar tvarN | Atfun ast_t ast_t | Attup (ast_t list)
        | Atapp (ast_t list) ((modN, typeN) id)
End
-/
inductive ast_t where
  | Atvar : tvarN → ast_t
  | Atfun : ast_t → ast_t → ast_t
  | Attup : List ast_t → ast_t
  | Atapp : List ast_t → cml_id modN typeN → ast_t
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  pat = Pany | Pvar varN | Plit lit
      | Pcon (((modN, conN) id) option) (pat list)
      | Pref pat | Pas pat varN | Ptannot pat ast_t
End
-/
inductive pat where
  | Pany : pat
  | Pvar : varN → pat
  | Plit : lit → pat
  | Pcon : Option (cml_id modN conN) → List pat → pat
  | Pref : pat → pat
  | Pas : pat → varN → pat
  | Ptannot : pat → ast_t → pat
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  lop = Andalso | Orelse
End
-/
inductive lop where
  | Andalso | Orelse
deriving Repr, BEq, Inhabited

/- HOL4:
Datatype:
  exp = Raise exp | Handle exp ((pat # exp) list) | Lit lit
      | Con (((modN, conN)id)option) (exp list) | Var ((modN, varN) id)
      | Fun varN exp | App op (exp list) | Log lop exp exp | If exp exp exp
      | Mat exp ((pat # exp) list)
      | Let (varN option) exp exp
      | Letrec ((varN # varN # exp) list) exp
      | Tannot exp ast_t | Lannot exp locs
End
-/
inductive exp where
  | Raise : exp → exp
  | Handle : exp → List (pat × exp) → exp
  | Lit : lit → exp
  | Con : Option (cml_id modN conN) → List exp → exp
  | Var : cml_id modN varN → exp
  | Fun : varN → exp → exp
  | App : op → List exp → exp
  | Log : lop → exp → exp → exp
  | If : exp → exp → exp → exp
  | Mat : exp → List (pat × exp) → exp
  | Let : Option varN → exp → exp → exp
  | Letrec : List (varN × varN × exp) → exp → exp
  | Tannot : exp → ast_t → exp
  | Lannot : exp → locs → exp
deriving Repr, BEq, Inhabited

/- HOL4:
Type type_def = ``: ( tvarN list # typeN # (conN # ast_t list) list) list``
-/
abbrev type_def := List (List tvarN × typeN × List (conN × List ast_t))

/- HOL4:
Datatype:
  dec = Dlet locs pat exp | Dletrec locs ((varN # varN # exp) list)
      | Dtype locs type_def | Dtabbrev locs (tvarN list) typeN ast_t
      | Dexn locs conN (ast_t list) | Dmod modN (dec list)
      | Dlocal (dec list) (dec list) | Denv tvarN
End
-/
inductive dec where
  | Dlet : locs → pat → exp → dec
  | Dletrec : locs → List (varN × varN × exp) → dec
  | Dtype : locs → type_def → dec
  | Dtabbrev : locs → List tvarN → typeN → ast_t → dec
  | Dexn : locs → conN → List ast_t → dec
  | Dmod : modN → List dec → dec
  | Dlocal : List dec → List dec → dec
  | Denv : tvarN → dec
deriving Repr, BEq, Inhabited

/- HOL4:
Definition pat_bindings_def:
  pat_bindings Pany already_bound = already_bound ∧
  pat_bindings (Pvar n) already_bound = n::already_bound ∧ ...
End
-/
mutual
def pat_bindings : pat → List varN → List varN
  | .Pany, ab => ab
  | .Pvar n, ab => n :: ab
  | .Plit _, ab => ab
  | .Pcon _ ps, ab => pats_bindings ps ab
  | .Pref p, ab => pat_bindings p ab
  | .Pas p i, ab => pat_bindings p (i :: ab)
  | .Ptannot p _, ab => pat_bindings p ab

def pats_bindings : List pat → List varN → List varN
  | [], ab => ab
  | p :: ps, ab => pats_bindings ps (pat_bindings p ab)
end

/- HOL4:
Definition every_exp_def[simp]:
  (every_exp p (Raise e) ⇔ p (Raise e) ∧ every_exp p e) ∧ ...
End
-/
def every_exp (p : exp → Bool) : exp → Bool
  | .Raise e => p (.Raise e) && every_exp p e
  | .Handle e pes =>
    p (.Handle e pes) && every_exp p e &&
      pes.attach.all fun ⟨⟨_, e'⟩, _⟩ => every_exp p e'
  | .Lit l => p (.Lit l)
  | .Con cn es => p (.Con cn es) && es.attach.all fun ⟨e', _⟩ => every_exp p e'
  | .Var v => p (.Var v)
  | .Fun x e => p (.Fun x e) && every_exp p e
  | .App o es => p (.App o es) && es.attach.all fun ⟨e', _⟩ => every_exp p e'
  | .Log l e1 e2 => p (.Log l e1 e2) && every_exp p e1 && every_exp p e2
  | .If e1 e2 e3 => p (.If e1 e2 e3) && every_exp p e1 && every_exp p e2 && every_exp p e3
  | .Mat e pes =>
    p (.Mat e pes) && every_exp p e &&
      pes.attach.all fun ⟨⟨_, e'⟩, _⟩ => every_exp p e'
  | .Let x e1 e2 => p (.Let x e1 e2) && every_exp p e1 && every_exp p e2
  | .Tannot e a => p (.Tannot e a) && every_exp p e
  | .Lannot e a => p (.Lannot e a) && every_exp p e
  | .Letrec funs e =>
    p (.Letrec funs e) && every_exp p e &&
      funs.attach.all fun ⟨⟨_, _, e'⟩, _⟩ => every_exp p e'
  termination_by e => sizeOf e
  decreasing_by
    all_goals first
      | decreasing_trivial
      | (simp_wf
         rename_i h
         have := List.sizeOf_lt_of_mem h
         simp at this
         omega)
