"""Typed Python -> executable Lean `Except`/`do`, with checked MVC proofs.

The shared Dafny admission pass supplies the existing Python alias/binding boundary;
no Dafny proof result is consulted. Lean independently checks the generated program's
Hoare theorem and every loop invariant. Unsupported syntax fails closed.
"""
from __future__ import annotations
import ast
from dataclasses import dataclass
from veripy.frontend.records import record_schemas
from veripy.backends.dafny.encoder import EncodeError


def ident(s): return '«'+s+'»'
def fail(n, message): raise EncodeError(message, getattr(n,'lineno',None), rule='lean-imperative')

@dataclass(frozen=True)
class Ty:
    kind: str
    args: tuple = ()
    def lean(self):
        if self.kind in ('list','seqtuple'): return '(List '+self.args[0].lean()+')'
        if self.kind=='tuple': return '('+' × '.join(t.lean() for t in self.args)+')'
        if self.kind=='opt': return '(Option '+self.args[0].lean()+')'
        return {'int':'Int','bool':'Bool','str':'(List Nat)','none':'Unit'}.get(self.kind,ident(self.kind))
I=Ty('int');B=Ty('bool');S=Ty('str');U=Ty('none')

def annotation(n):
    if isinstance(n,ast.Name):return Ty(n.id)
    if isinstance(n,ast.Constant) and n.value is None:return U
    if isinstance(n,ast.Subscript) and isinstance(n.value,ast.Name):
        items=n.slice.elts if isinstance(n.slice,ast.Tuple) else [n.slice]
        return Ty({'List':'list','Tuple':'tuple','Optional':'opt'}.get(n.value.id,n.value.id),tuple(annotation(x) for x in items))
    if isinstance(n,ast.BinOp) and isinstance(n.op,ast.BitOr):
        if isinstance(n.right,ast.Constant) and n.right.value is None:return Ty('opt',(annotation(n.left),))
    fail(n,'unsupported Lean imperative type annotation')

PRELUDE = r'''import Lean
import Std.Tactic.Do
open Std.Do
def VeriPy.loopTag {α : Type} (_id : Nat) (xs : List α) : List α := xs
theorem VeriPy.continueFacts {α : Type} {r : Option α} {C : Prop} {Q : α → Prop}
    (h : r=none ∧ C ∨ ∃ a, r=some a ∧ Q a) (hn : r=none) : C := by
  rcases h with h | ⟨a,ha,_⟩
  · exact h.2
  · rw [hn] at ha; contradiction
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open Lean Meta Elab Tactic in
elab "veripy_loop_tag " id:num : tactic => withMainContext do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  unless target.isAppOfArity ``Std.Do.Invariant 4 do throwError "not a loop invariant"
  let iterator := target.getArg! 1
  unless iterator.isAppOfArity ``VeriPy.loopTag 3 && iterator.getArg! 1 == mkNatLit id.getNat do
    throwError "different loop"
open Lean Elab Tactic in
elab "veripy_let " name:ident " := " value:term : tactic => Term.withoutErrToSorry do
  evalTactic (← `(tactic| let $name := $value))
open Lean Meta Elab Tactic in
elab "veripy_split_cursor" : tactic => withMainContext do
  let goal ← getMainGoal
  for decl in ← getLCtx do
    let type ← instantiateMVars decl.type
    if type.isAppOfArity ``And 2 && ((type.getArg! 0).isAppOfArity ``Eq 3 || (type.getArg! 1).isAppOfArity ``Eq 3 || (type.getArg! 1).isAppOfArity ``And 2 || (type.getArg! 1).isAppOfArity ``Not 1) then
      let branches ← goal.cases decl.fvarId
      replaceMainGoal (branches.toList.map (·.mvarId))
      return
  throwError "no cursor conjunction"
open Lean Meta Elab Tactic in
elab "veripy_split_goal" : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType)
  unless type.isAppOfArity ``And 2 do throwError "not a structural conjunction"
  replaceMainGoal (← goal.apply (mkConst ``And.intro))
open Lean Meta Elab Tactic in
elab "veripy_capture " name:ident : tactic => withMainContext do
  let mut found : Option FVarId := none
  for decl in ← getLCtx do
    if decl.userName.eraseMacroScopes == name.getId.eraseMacroScopes then
      found := some decl.fvarId
  let some id := found | throwError "local not found: {name}"
  replaceMainGoal [← (← getMainGoal).rename id name.getId]
open Lean Meta Elab Tactic in
elab "veripy_capture_type " name:ident " : " ty:term : tactic => withMainContext do
  let expected ← Lean.Elab.Term.elabType ty
  let mut found : Option FVarId := none
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      if ← isDefEq decl.type expected then found := some decl.fvarId
  let some id := found | throwError "no local with the requested capture type"
  let value := mkFVar id
  let goal ← (← getMainGoal).define name.getId (← inferType value) value
  let (alias, goal) ← goal.intro1
  replaceMainGoal [← goal.rename alias name.getId]
open Lean Meta Elab Tactic in
elab "veripy_cursor " name:ident tag:num mode:num component:num arity:num : tactic => withMainContext do
  let mut found : Option Expr := none
  for decl in ← getLCtx do
    let type ← instantiateMVars decl.type
    if type.isAppOfArity ``Eq 3 then
      let left := type.getArg! 1
      let right := type.getArg! 2
      if left.isAppOfArity ``VeriPy.loopTag 3 && left.getArg! 1 == mkNatLit tag.getNat then
        let parts := if right.isAppOfArity ``List.append 3 then
          some (right.getArg! 1, right.getArg! 2)
          else if right.isAppOfArity ``HAppend.hAppend 6 then
          some (right.getArg! 4, right.getArg! 5)
          else none
        let some (pref, tail) := parts | continue
        if tail.isAppOfArity ``List.cons 3 then
          if mode.getNat == 1 then
            found := some (← mkAppM ``Int.ofNat #[← mkAppM ``List.length #[pref]])
          else
            let mut value := tail.getArg! 1
            if arity.getNat > 0 then
              for _ in [:component.getNat] do value := mkProj ``Prod 1 value
              if component.getNat + 1 < arity.getNat then value := mkProj ``Prod 0 value
            found := some value
  let some value := found | throwError "source loop cursor is unavailable"
  let goal ← (← getMainGoal).define name.getId (← inferType value) value
  let (alias, goal) ← goal.intro1
  replaceMainGoal [← goal.rename alias name.getId]
open Lean Meta Elab Tactic in
elab "veripy_clear_aux" : tactic => withMainContext do
  let mut goal ← getMainGoal
  let mut declarations : List LocalDecl := []
  for decl in ← getLCtx do declarations := decl :: declarations
  for decl in declarations do
    if decl.isImplementationDetail || decl.userName.eraseMacroScopes.toString.startsWith "__do_jp" then
      try goal ← goal.clear decl.fvarId catch _ => pure ()
  replaceMainGoal [goal]
open Lean Meta Elab Tactic in
elab "veripy_continue_facts" : tactic => withMainContext do
  let mut goal ← getMainGoal
  for decl in ← getLCtx do
    let type ← instantiateMVars decl.type
    if type.isAppOfArity ``Or 2 && (type.getArg! 0).isAppOfArity ``And 2 then
      let condition := (type.getArg! 0).getArg! 0
      if condition.isAppOfArity ``Eq 3 then
        for known in ← getLCtx do
          if ← isDefEq known.type condition then
            try
              let proof ← mkAppM ``VeriPy.continueFacts #[mkFVar decl.fvarId, mkFVar known.fvarId]
              let (_, next) ← goal.note (← mkFreshUserName `vp_continued) proof
              goal := next
            catch _ => pure ()
  replaceMainGoal [goal]
open Lean Meta Elab Tactic in
elab "veripy_project_facts" : tactic => withMainContext do
  let mut goal ← getMainGoal
  let mut pending : List Expr := []
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do pending := mkFVar decl.fvarId :: pending
  let mut fuel := 1024
  while !pending.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let proof := pending.head!
    pending := pending.tail!
    let type ← whnf (← inferType proof)
    if type.isAppOfArity ``And 2 then
      let left ← mkAppM ``And.left #[proof]
      let right ← mkAppM ``And.right #[proof]
      let (_, next) ← goal.note (← mkFreshUserName `vp_fact) left
      goal := next
      let (_, next) ← goal.note (← mkFreshUserName `vp_fact) right
      goal := next
      pending := left :: right :: pending
  replaceMainGoal [goal]
open Lean Meta Elab Tactic in
elab "veripy_fold_projections" : tactic => withMainContext do
  let mut goal ← getMainGoal
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let folded ← Sym.foldProjs decl.type
      unless ← isDefEq decl.type folded do throwError "projection normalization changed a type"
      goal ← goal.replaceLocalDeclDefEq decl.fvarId folded
  goal ← goal.change (← Sym.foldProjs (← goal.getType))
  replaceMainGoal [goal]
namespace VeriPy
theorem ofNat_cast (n : Nat) : Int.ofNat n = (n : Int) := rfl
inductive Error where
  | value | index | zero | assertion | type
  deriving Repr, DecidableEq, Inhabited


def raise {α : Type} (e : Error) : Except Error α := MonadExceptOf.throw e
@[spec] theorem raise_spec {α : Type} (e : Error) (Q : PostCond α (.except Error .pure)) :
    Triple (ps := .except Error .pure) (raise e : Except Error α) (spred(Q.2.1 e)) Q := by simp [Triple.iff, raise]

def get [Inhabited α] (xs : List α) (i : Int) : Except Error α :=
  if 0 ≤ i ∧ i < xs.length then pure (xs.getD i.toNat default) else raise Error.index

def set (xs : List α) (i : Int) (x : α) : Except Error (List α) :=
  if 0 ≤ i ∧ i < xs.length then pure (xs.set i.toNat x) else raise Error.index

def getPython [Inhabited α] (xs : List α) (i : Int) : Except Error α :=
  get xs (if i < 0 then Int.ofNat xs.length + i else i)

def setPython (xs : List α) (i : Int) (x : α) : Except Error (List α) :=
  set xs (if i < 0 then Int.ofNat xs.length + i else i) x

def requireSome [Inhabited α] (value : Option α) : Except Error α :=
  match value with | some x => pure x | none => raise Error.type

def maximum (xs : List Int) : Except Error Int :=
  if xs = [] then raise Error.value else pure (xs.foldl max (xs.headD 0))

def divmod (x y : Int) : Except Error (Int × Int) :=
  if y = 0 then raise Error.zero else pure (Int.fdiv x y, Int.fmod x y)

def div (x y : Int) : Except Error Int :=
  if y = 0 then raise Error.zero else pure (Int.fdiv x y)

def mod (x y : Int) : Except Error Int :=
  if y = 0 then raise Error.zero else pure (Int.fmod x y)

def lexInts : List Int → List Int → Bool
  | [], _ => true
  | _::_, [] => false
  | a::as, b::bs => if a<b then true else if a=b then lexInts as bs else false

def bisectRightAux [Inhabited α] (le : α → α → Bool) (xs : List α) (x : α) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if lo<hi then
      let mid := (lo+hi)/2
      if le (xs.getD mid default) x then bisectRightAux le xs x fuel (mid+1) hi
      else bisectRightAux le xs x fuel lo mid
    else lo

def bisectRight [Inhabited α] (le : α → α → Bool) (xs : List α) (x : α) : Nat :=
  bisectRightAux le xs x (xs.length+1) 0 xs.length

def insort [Inhabited α] (le : α → α → Bool) (xs : List α) (x : α) : List α :=
  let i := bisectRight le xs x
  xs.take i ++ x :: xs.drop i

def allChecked (f : α → Except Error Bool) (_model : α → Bool) : List α → Except Error Bool
  | [] => .ok true
  | x::xs => do if (← f x) then allChecked f _model xs else return false

def anyChecked (f : α → Except Error Bool) (_model : α → Bool) : List α → Except Error Bool
  | [] => .ok false
  | x::xs => do if (← f x) then return true else anyChecked f _model xs

def range (lo hi : Int) : List Int := (List.range (hi-lo).toNat).map (fun n => lo + Int.ofNat n)

def slice (xs : List α) (lo hi : Int) : List α :=
  let start := if lo < 0 then max 0 (xs.length + lo) else lo
  let stop := if hi < 0 then max 0 (xs.length + hi) else hi
  (xs.take stop.toNat).drop start.toNat
end VeriPy
def VeriPy.mapChecked (f : α → Except VeriPy.Error β) (_model : α → β) (xs : List α) : Except VeriPy.Error (List β) := xs.mapM f
@[spec] theorem VeriPy.mapChecked_spec (f : α → Except VeriPy.Error β) (model : α → β) (xs : List α)
    (h : ∀ x ∈ xs, f x = Except.ok (model x)) :
    ⦃⌜True⌝⦄ VeriPy.mapChecked f model xs ⦃(fun result => ⌜result = xs.map model⌝, fun (_ : VeriPy.Error) => ⌜False⌝, ())⦄ := by
  have he : xs.mapM f = Except.ok (xs.map model) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      rw [List.mapM_cons, hx, ht]
      rfl
  rw [VeriPy.mapChecked, he]
  apply Triple.pure
  simp

@[spec] theorem VeriPy.allChecked_spec (f : α → Except VeriPy.Error Bool) (model : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, f x = Except.ok (model x)) :
    ⦃⌜True⌝⦄ VeriPy.allChecked f model xs ⦃(fun result => ⌜result = xs.all model⌝, fun (_ : VeriPy.Error) => ⌜False⌝, ())⦄ := by
  have he : VeriPy.allChecked f model xs = Except.ok (xs.all model) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [VeriPy.allChecked, hx, ht, List.all_cons]
      cases model x <;> rfl
  rw [he]
  apply Triple.pure
  simp

@[spec] theorem VeriPy.anyChecked_spec (f : α → Except VeriPy.Error Bool) (model : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, f x = Except.ok (model x)) :
    ⦃⌜True⌝⦄ VeriPy.anyChecked f model xs ⦃(fun result => ⌜result = xs.any model⌝, fun (_ : VeriPy.Error) => ⌜False⌝, ())⦄ := by
  have he : VeriPy.anyChecked f model xs = Except.ok (xs.any model) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [VeriPy.anyChecked, hx, ht, List.any_cons]
      cases model x <;> rfl
  rw [he]
  apply Triple.pure
  simp
'''

class Compiler:
    def __init__(self, source, specs, proof_lemmas):
        self.source=source;self.specs=specs;self.module=ast.parse(source)
        from veripy.backends.dafny.environment import resolve_for_encoder
        environment=resolve_for_encoder(self.module)
        self.exceptions=environment.exceptions
        self.module_values=environment.values;self.shadowed=set();self.break_flags=[]
        # Keep the established lowering untouched outside explicitly modeled
        # exception modules. Resolution is static and never imports user code.
        if self.exceptions:self.module=environment.module
        from veripy.frontend.fixed_loops import lower_fixed_loops
        self.module=lower_fixed_loops(self.module,specs)
        self.records=record_schemas(self.module)
        self.fields={n:{f:annotation(t) for f,t in fs} for n,fs in self.records.items()}
        self.fns={n.name:n for n in self.module.body if isinstance(n,ast.FunctionDef)}
        self.returns={n:annotation(f.returns) for n,f in self.fns.items()}
        self.proof_lemmas=proof_lemmas;self.proof_hints=getattr(proof_lemmas,'theorems',proof_lemmas);self.lines=PRELUDE.splitlines();self.line_map={};self.theorems=[]
        if any(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=="int" for n in ast.walk(self.module)):
            from veripy.backends.lean.decimal import prelude
            self.lines.extend(prelude().splitlines())
        if any((isinstance(n,ast.Call) and ((isinstance(n.func,ast.Name) and n.func.id in ('tuple','reversed')) or (isinstance(n.func,ast.Attribute) and n.func.attr in ('index','find')))) or (isinstance(n,ast.Slice) and n.step is not None) for n in ast.walk(self.module)):
            from veripy.backends.lean.sequences import PRELUDE as sequence_prelude
            self.lines.extend(sequence_prelude.splitlines())
        if self.exceptions:
            index=self.lines.index('  | value | index | zero | assertion | type')
            self.lines[index]+=' | custom (tag : Nat)'
        self.env={};self.renames={};self.loop_index=None;self.result_type=U;self.spec=False;self.invariants=[];self.invariant_defs=[];self.invariant_tags=[];self.loop_origins={};self.nonnegative=set();self.capture_models={}
    def emit(self,s,line=None):
        for part in s.splitlines():
            self.lines.append(part)
            if line:self.line_map[len(self.lines)]=line
    def typ(self,n):
        if isinstance(n,ast.Name):
            if n.id=='result':return self.result_type
            if n.id not in self.env and n.id not in self.shadowed and n.id in self.module_values:
                from veripy.backends.dafny.environment import literal
                return self.typ(literal(self.module_values[n.id],n))
            if n.id not in self.env:fail(n,'unknown name '+n.id)
            return self.env[n.id]
        if isinstance(n,ast.Constant):return U if n.value is None else B if type(n.value)is bool else I if type(n.value)is int else S
        if isinstance(n,ast.Attribute):
            if isinstance(n.value,ast.Name) and n.value.id=='sys' and n.attr=='maxsize':return I
            return self.fields[self.typ(n.value).kind][n.attr]
        if isinstance(n,(ast.List,ast.Tuple)):
            return Ty('tuple',tuple(self.typ(x) for x in n.elts)) if isinstance(n,ast.Tuple) else Ty('list',(self.typ(n.elts[0]) if n.elts else I,))
        if isinstance(n,ast.Subscript):
            t=self.typ(n.value)
            if isinstance(n.slice,ast.Slice):return t
            if t.kind=='opt':t=t.args[0]
            if t.kind=='tuple':return t.args[ast.literal_eval(n.slice)]
            return S if t.kind=='str' else t.args[0]
        if isinstance(n,ast.BinOp):return self.typ(n.left)
        if isinstance(n,(ast.Compare,ast.BoolOp)):return B
        if isinstance(n,ast.UnaryOp):return B if isinstance(n.op,ast.Not) else self.typ(n.operand)
        if isinstance(n,ast.IfExp):
            a=self.typ(n.body);b=self.typ(n.orelse)
            return b if a.kind in ('none','opt') and b.kind not in ('none','opt') else a
        if isinstance(n,ast.Call):
            if isinstance(n.func,ast.Name):
                if n.func.id in ('len','sum','prod','min','max','abs','loop_index','int','bisect_right'):return I
                if n.func.id in ('all','any','raised','ghost','bool','decimal_valid'):return B
                if n.func.id=='divmod':return Ty('tuple',(I,I))
                if n.func.id=='str' and len(n.args)==1 and self.typ(n.args[0])==S:return S
                if n.func.id in ('tuple','reversed') and len(n.args)==1:return Ty('seqtuple',(self.iter_type(n.args[0]),))
                if n.func.id in ('old','sorted'):return self.typ(n.args[0])
                if n.func.id in self.returns:return self.returns[n.func.id]
                if n.func.id in self.fields:return Ty(n.func.id)
                if n.func.id=='range':return Ty('list',(I,))
                if n.func.id=='enumerate':return Ty('list',(Ty('tuple',(I,self.typ(n.args[0]).args[0])),))
            if isinstance(n.func,ast.Attribute):
                if isinstance(n.func.value,ast.Name) and n.func.value.id=='math' and n.func.attr=='prod':return I
                if n.func.attr in ('count','index','find'):return I
                if n.func.attr in ('endswith','startswith'):return B
                if n.func.attr=='split':return Ty('list',(S,))
        if isinstance(n,(ast.ListComp,ast.GeneratorExp)):
            g=n.generators[0];old=self.env.copy();self.bind_type(g.target,self.iter_type(g.iter));t=self.typ(n.elt);self.env=old;return Ty('list',(t,))
        fail(n,'unsupported expression type '+ast.dump(n))
    def iter_type(self,n):
        t=self.typ(n)
        if t==S:return S
        if t.kind in ('list','seqtuple'):return t.args[0]
        fail(n,'iteration requires a homogeneous sequence')
    def iter_expr(self,n):
        value=self.expr(n)
        return f'(({value}).map (fun c => [c]))' if self.typ(n)==S else value
    def bind_type(self,target,t):
        if isinstance(target,ast.Name):self.env[target.id]=t;return
        if isinstance(target,ast.Tuple) and t.kind=='tuple':
            for x,y in zip(target.elts,t.args):self.bind_type(x,y)
            return
        fail(target,'unsupported assignment target')
    def prop(self,n):
        from veripy.frontend.literal_map import expand_literal_map
        try: expanded=expand_literal_map(n,self.fns)
        except ValueError as exc: fail(n,str(exc))
        if expanded is not None:
            if self.typ(n.args[0].args[1])!=S:fail(n,'literal predicate map requires a string iterable')
            return self.prop(expanded)
        if not self.spec and isinstance(n,ast.BoolOp) and not self.total_boolean(n):return '('+self.runtime_bool(n)+' = true)'
        if isinstance(n,ast.Constant) and type(n.value)is bool:return str(n.value)
        if isinstance(n,ast.BoolOp):return '('+(' ∧ ' if isinstance(n.op,ast.And) else ' ∨ ').join(self.prop(x) for x in n.values)+')'
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.Not):return '(¬ '+self.prop(n.operand)+')'
        if isinstance(n,ast.Compare):
            parts=[]
            for l,op,r in zip([n.left,*n.comparators],n.ops,n.comparators):
                if isinstance(op,(ast.Eq,ast.NotEq)) and self.typ(l)==B and self.typ(r)==B:
                    relation=f'({self.prop(l)} ↔ {self.prop(r)})'
                    parts.append(relation if isinstance(op,ast.Eq) else '(¬ '+relation+')')
                    continue
                a=self.expr(l);b=self.expr(r)
                if isinstance(op,(ast.In,ast.NotIn)) and self.typ(r)==S:
                    if self.typ(l)!=S:fail(n,'string membership requires a string')
                    parts.append(f'(({a}).isInfixOf_internal {b} = '+('true' if isinstance(op,ast.In) else 'false')+')')
                    continue
                if not isinstance(op,(ast.Is,ast.IsNot)):
                    if self.typ(l).kind=='opt' and self.typ(r).kind not in ('opt','none'):a=self.unwrap(l)
                    if self.typ(r).kind=='opt' and self.typ(l).kind not in ('opt','none'):b=self.unwrap(r)
                if isinstance(op,(ast.Is,ast.IsNot)):
                    if not isinstance(r,ast.Constant) or r.value is not None:fail(n,'identity only supports None')
                    parts.append(f'({a} '+('=' if isinstance(op,ast.Is) else '≠')+' none)')
                else:
                    symbol={ast.Eq:'=',ast.NotEq:'≠',ast.Lt:'<',ast.LtE:'≤',ast.Gt:'>',ast.GtE:'≥',ast.In:'∈',ast.NotIn:'∉'}.get(type(op))
                    if not symbol:fail(n,'unsupported comparison')
                    parts.append(f'({a} {symbol} {b})')
            return '('+' ∧ '.join(parts)+')'
        if isinstance(n,ast.Call) and isinstance(n.func,ast.Name):
            if n.func.id=='bool' and len(n.args)==1:return self.prop(n.args[0])
            if n.func.id=='decimal_valid' and self.spec:return '(VeriPy.tryDecimal '+self.expr(n.args[0])+' ≠ none)'
            if n.func.id=='raised':
                state=self.renames.get('raised','False')
                if n.args and self.exceptions and state!='False':
                    return self.matches_error('__vp_error',n.args[0].value,n)
                return state
            if n.func.id=='ghost':
                if not self.spec or not n.args or not isinstance(n.args[0],ast.Constant) or n.args[0].value not in self.proof_lemmas:fail(n,'unknown ghost predicate')
                return '('+ident(n.args[0].value)+' '+' '.join(self.expr(x) for x in n.args[1:])+')'
            if self.spec and n.func.id in ('all','any') and isinstance(n.args[0],ast.GeneratorExp):
                return self.quantified(n.args[0].generators,n.args[0].elt,n.func.id=='all')
        t=self.typ(n);e=self.expr(n)
        if t.kind=='bool':return f'({e} = true)'
        if t.kind in ('list','str','seqtuple'):return f'({e} ≠ [])'
        if t.kind=='int':return f'({e} ≠ 0)'
        if t.kind=='tuple':return 'True' if t.args else 'False'
        if t.kind=='opt':
            if t.args[0].kind=='tuple' and t.args[0].args:return f'({e} ≠ none)'
            fail(n,'optional truthiness requires a nonempty tuple')
        fail(n,'unsupported truthiness')
    def quantified(self,generators,element,universal):
        if not generators:return self.prop(element)
        g,*rest=generators
        if g.ifs or g.is_async:fail(g.iter,'filtered or async quantified generators are not supported')
        old=self.env.copy();old_nonnegative=self.nonnegative.copy()
        seq=self.iter_expr(g.iter)
        ranged=isinstance(g.iter,ast.Call) and isinstance(g.iter.func,ast.Name) and g.iter.func.id=='range'
        if ranged:
            args=g.iter.args
            if len(args) not in (1,2):fail(g.iter,'range steps pending')
            lo='0' if len(args)==1 else self.expr(args[0]);hi=self.expr(args[-1])
        self.bind_type(g.target,self.iter_type(g.iter));binder=self.pattern(g.target)
        if ranged and isinstance(g.target,ast.Name):
            lower=ast.Constant(0) if len(g.iter.args)==1 else g.iter.args[0]
            if self.is_nonnegative(lower):self.nonnegative.add(g.target.id)
        body=self.quantified(rest,element,universal)
        self.env=old;self.nonnegative=old_nonnegative
        quantifier='∀' if universal else '∃'
        if ranged:return f'({quantifier} {binder} : Int, ({lo} ≤ {binder} ∧ {binder} < {hi}) '+('→' if universal else '∧')+' '+body+')'
        return f'({quantifier} {binder} ∈ {seq}, {body})'
    def unwrap(self,n):
        e=self.expr(n)
        default='(0 : Int)' if self.typ(n).args[0]==I else 'default'
        return f'({e}).getD {default}' if self.spec else f'(← VeriPy.requireSome {e})'
    def total_boolean(self,n):
        # Only fixed-loop guards opt into this initial optimization. These
        # primitive reads/comparisons cannot raise or have observable effects.
        if not getattr(self,'pure_guards',False):return False
        allowed=(ast.Name,ast.Constant,ast.Load,ast.BoolOp,ast.And,ast.Or,
                 ast.UnaryOp,ast.Not,ast.Compare,ast.Eq,ast.NotEq,
                 ast.Lt,ast.LtE,ast.Gt,ast.GtE)
        for node in ast.walk(n):
            if not isinstance(node,allowed):return False
            if isinstance(node,(ast.Name,ast.Constant)) and self.typ(node) not in (I,B,S):return False
        return True
    def runtime_bool(self,n):
        if not isinstance(n,ast.BoolOp) or self.total_boolean(n):return '(decide '+self.prop(n)+')'
        first,*rest=n.values
        remainder=rest[0] if len(rest)==1 else ast.BoolOp(op=n.op,values=rest)
        condition=self.prop(first);tail=self.runtime_bool(remainder)
        if isinstance(n.op,ast.And):body=f'if {condition} then return {tail} else return false'
        else:body=f'if {condition} then return true else return {tail}'
        return f'(← (do {body} : Except VeriPy.Error Bool))'
    def expr(self,n):
        from veripy.frontend.literal_map import expand_literal_map
        try: expanded=expand_literal_map(n,self.fns)
        except ValueError as exc: fail(n,str(exc))
        if expanded is not None:
            if self.typ(n.args[0].args[1])!=S:fail(n,'literal predicate map requires a string iterable')
            return self.expr(expanded)
        if isinstance(n,ast.Name):
            if n.id not in self.env and n.id not in self.shadowed and n.id in self.module_values:
                from veripy.backends.dafny.environment import literal
                return self.expr(literal(self.module_values[n.id],n))
            return self.renames.get(n.id,ident(n.id))
        if isinstance(n,ast.Constant):
            if n.value is None:return 'none'
            if type(n.value)is bool:return str(n.value).lower()
            if type(n.value)is int:return f'({n.value} : Int)'
            if type(n.value)is str:
                return '(['+', '.join(str(ord(c)) for c in n.value)+'] : List Nat)'
        if isinstance(n,ast.Attribute):
            if isinstance(n.value,ast.Name) and n.value.id=='sys' and n.attr=='maxsize':return '(9223372036854775807 : Int)'
            return f'({self.expr(n.value)}).{ident(n.attr)}'
        if isinstance(n,ast.Tuple):return '('+', '.join(self.expr(x) for x in n.elts)+')'
        if isinstance(n,ast.List):return '['+', '.join(self.expr(x) for x in n.elts)+']'
        if isinstance(n,ast.UnaryOp):
            if isinstance(n.op,ast.Not):return '(decide '+self.prop(n)+')'
            if isinstance(n.op,ast.UAdd):return self.expr(n.operand)
            if isinstance(n.op,ast.USub):return '(-'+self.expr(n.operand)+')'
            fail(n,'unsupported unary operation')
        if isinstance(n,ast.BoolOp) and not self.spec:
            if not all(self.typ(x)==B for x in n.values):fail(n,'non-Boolean operand-returning and/or pending')
            return self.runtime_bool(n)
        if isinstance(n,(ast.Compare,ast.BoolOp)):return '(decide '+self.prop(n)+')'
        if isinstance(n,ast.BinOp):
            a=self.expr(n.left);b=self.expr(n.right)
            if isinstance(n.op,ast.Mult) and self.typ(n.left).kind=='list':
                if not isinstance(n.left,ast.List) or len(n.left.elts)!=1:fail(n,'only singleton list repetition')
                return f'(List.replicate ({b}).toNat {self.expr(n.left.elts[0])})'
            if isinstance(n.op,(ast.FloorDiv,ast.Mod)):
                name='fdiv' if isinstance(n.op,ast.FloorDiv) else 'fmod'
                return f'(Int.{name} {a} {b})' if self.spec else f'(← VeriPy.{"div" if name=="fdiv" else "mod"} {a} {b})'
            symbol={ast.Add:'++' if self.typ(n.left).kind in ('list','str','seqtuple') else '+',ast.Sub:'-',ast.Mult:'*'}.get(type(n.op))
            if symbol:return f'({a} {symbol} {b})'
        if isinstance(n,ast.Subscript):
            v=self.expr(n.value);t=self.typ(n.value)
            if t.kind=='opt':v=self.unwrap(n.value);t=t.args[0]
            if isinstance(n.slice,ast.Slice):
                if n.slice.step is not None:
                    if not isinstance(n.slice.step,ast.Constant) or type(n.slice.step.value)is not int or n.slice.step.value<=0:
                        fail(n,'slice stride requires a positive integer literal')
                    lo=self.expr(n.slice.lower) if n.slice.lower else '0';hi=self.expr(n.slice.upper) if n.slice.upper else f'({v}).length'
                    return f'(VeriPy.stride {v} {lo} {hi} {n.slice.step.value})'
                lo=self.expr(n.slice.lower) if n.slice.lower else '0';hi=self.expr(n.slice.upper) if n.slice.upper else f'({v}).length'
                return f'(VeriPy.slice {v} {lo} {hi})'
            if t.kind=='tuple':
                i=ast.literal_eval(n.slice)
                if type(i)is not int or not -len(t.args)<=i<len(t.args):fail(n,'tuple index out of bounds')
                if i<0:i+=len(t.args)
                return '('+v+')'+'.2'*i+('' if i==len(t.args)-1 else '.1')
            idx=self.expr(n.slice)
            direct=self.is_nonnegative(n.slice)
            normalized=idx if direct else f'(if {idx} < 0 then Int.ofNat ({v}).length + {idx} else {idx})'
            read=f'(({v}).getD ({normalized}).toNat default)' if self.spec else f'(← VeriPy.{"get" if direct else "getPython"} {v} {idx})'
            return '['+read+']' if t.kind=='str' else read
        if isinstance(n,ast.IfExp):
            a=self.expr(n.body);b=self.expr(n.orelse)
            if self.typ(n.body).kind=='opt' and self.typ(n).kind!='opt':a=self.unwrap(n.body)
            if self.typ(n.orelse).kind=='opt' and self.typ(n).kind!='opt':b=self.unwrap(n.orelse)
            condition=self.prop(n.test)
            if not self.spec and ('←' in a or '←' in b):
                return f'(← (do if {condition} then return {a} else return {b} : Except VeriPy.Error {self.typ(n).lean()}))'
            return f'(if {condition} then {a} else {b})'
        if isinstance(n,ast.Call):
            if isinstance(n.func,ast.Name):
                name=n.func.id;args=n.args
                if name=='str' and len(args)==1 and not n.keywords and self.typ(args[0])==S:return self.expr(args[0])
                if name=='tuple' and len(args)==1 and not n.keywords:return self.iter_expr(args[0])
                if name=='reversed' and len(args)==1 and not n.keywords:return f'({self.iter_expr(args[0])}).reverse'
                if name=='divmod' and len(args)==2:
                    a=self.expr(args[0]);b=self.expr(args[1])
                    return f'(Int.fdiv {a} {b}, Int.fmod {a} {b})' if self.spec else f'(← VeriPy.divmod {a} {b})'
                if name=='int' and len(args)==1 and self.typ(args[0])==S:
                    value=self.expr(args[0])
                    return f'(VeriPy.tryDecimal {value}).getD 0' if self.spec else f'(← VeriPy.decimal {value})'
                if name=='bool' and len(args)==1:return '(decide '+self.prop(args[0])+')'
                if name=='divmod' and len(args)==2:
                    a,b=map(self.expr,args)
                    return f'(Int.fdiv {a} {b}, Int.fmod {a} {b})' if self.spec else f'(← VeriPy.divmod {a} {b})'
                if name in self.fields:
                    fields=list(self.fields[name]);bound={};steps=[]
                    supplied=list(zip(fields,args))+[(k.arg,k.value) for k in n.keywords]
                    if len(args)>len(fields) or any(k not in fields for k,_ in supplied) or len({k for k,_ in supplied})!=len(supplied) or len(supplied)!=len(fields):fail(n,'record construction requires each declared field exactly once')
                    for j,(key,value) in enumerate(supplied):
                        term=self.expr(value)
                        if not self.spec:
                            temporary=ident('__vp_field_'+str(n.lineno)+'_'+str(j))
                            steps.append('let '+temporary+' : '+self.fields[name][key].lean()+' := '+term)
                            bound[key]=temporary
                        else:bound[key]=term
                    result='({ '+', '.join(ident(k)+' := '+bound[k] for k in fields)+' } : '+ident(name)+')'
                    if self.spec:return result
                    return '(← (do '+'; '.join(steps)+'; return '+result+' : Except VeriPy.Error '+ident(name)+'))'
                if name in self.fns:
                    if self.spec:fail(n,'effectful helper call in a contract requires an explicit ghost predicate')
                    fn=self.fns[name];parameters=[*fn.args.args,*fn.args.kwonlyargs]
                    bound={a.arg:v for a,v in zip(fn.args.args,args)}
                    bound.update({k.arg:k.value for k in n.keywords})
                    defaults=dict(zip([a.arg for a in fn.args.args[-len(fn.args.defaults):]],fn.args.defaults)) if fn.args.defaults else {}
                    defaults.update({a.arg:d for a,d in zip(fn.args.kwonlyargs,fn.args.kw_defaults) if d is not None})
                    actual=[bound.get(a.arg,defaults.get(a.arg)) for a in parameters]
                    if any(x is None for x in actual):fail(n,'missing helper argument')
                    return '(← '+ident(name)+' '+' '.join(self.expr(x) for x in actual)+')'
                if name=='bisect_right' and len(args)==2 and not n.keywords:
                    t=self.typ(args[0]).args[0]
                    return '(Int.ofNat (VeriPy.bisectRight (fun a b => decide ('+self.ordered(t,'a','b')+')) '+self.expr(args[0])+' '+self.expr(args[1])+'))'
                if name=='sorted' and len(args)==1 and len(n.keywords)==1 and n.keywords[0].arg=='key':
                    key=n.keywords[0].value
                    if not isinstance(key,ast.Lambda) or len(key.args.args)!=1:fail(n,'sort key requires a one-argument lambda')
                    seq=self.expr(args[0]);old=self.env.copy();binder=key.args.args[0].arg
                    self.env[binder]=self.typ(args[0]).args[0]
                    mode=self.spec;self.spec=True;model=self.sort_key(key.body);self.spec=mode;body=self.sort_key(key.body);self.env=old
                    decorated='('+seq+').map (fun '+ident(binder)+' => ('+model+', '+ident(binder)+'))'
                    if '←' in body:decorated='(← VeriPy.mapChecked (fun '+ident(binder)+' => (do return ('+body+', '+ident(binder)+'))) (fun '+ident(binder)+' => ('+model+', '+ident(binder)+')) '+seq+')'
                    return '((('+decorated+').mergeSort (fun a b => VeriPy.lexInts a.1 b.1)).map Prod.snd)'
                if name=='sorted' and len(args)==1 and not n.keywords:
                    t=self.typ(args[0]).args[0]
                    return '(('+self.expr(args[0])+').mergeSort (fun a b => decide ('+self.ordered(t,'a','b')+')))'
                if name=='len':return f'(Int.ofNat ({self.expr(args[0])}).length)'
                if name=='max' and len(args)==1:
                    seq=self.expr(args[0])
                    return f'(({seq}).foldl max (({seq}).headD 0))' if self.spec else f'(← VeriPy.maximum {seq})'
                if name=='sum' and self.typ(args[0]).kind=='tuple':
                    t=self.typ(args[0])
                    if not t.args or any(x!=I for x in t.args):fail(n,'tuple sum requires nonempty integer tuple')
                    projections=['__vp_sum_tuple'+'.2'*i+('' if i==len(t.args)-1 else '.1') for i in range(len(t.args))]
                    return '(let __vp_sum_tuple := '+self.expr(args[0])+'; '+' + '.join(projections)+')'
                if name in ('sum','prod'):return f'({self.expr(args[0])}).{name}'
                if name=='enumerate' and len(args)==1:return '(('+self.expr(args[0])+').zipIdx.map (fun (x,i) => (Int.ofNat i,x)))'
                if name in ('min','max') and len(args)==2:return f'({name} {self.expr(args[0])} {self.expr(args[1])})'
                if name=='abs':return f'(Int.natAbs {self.expr(args[0])} : Int)'
                if name=='old':return self.renames.get('old:'+ast.unparse(args[0]),self.expr(args[0]))
                if name=='loop_index' and self.loop_index:return self.loop_index
                if name=='range' and len(args)in(1,2):return f'(VeriPy.range {"0" if len(args)==1 else self.expr(args[0])} {self.expr(args[-1])})'
                if name in ('all','any'):
                    if self.spec:return '(decide '+self.prop(n)+')'
                    if len(args[0].generators)!=1 or args[0].generators[0].ifs:fail(n,'runtime filtered or multi-generator quantifiers are not yet supported')
                    g=args[0].generators[0];seq=self.iter_expr(g.iter);old=self.env.copy();self.bind_type(g.target,self.iter_type(g.iter));body=self.runtime_bool(args[0].elt);self.spec=True;model='(decide '+self.prop(args[0].elt)+')';self.spec=False;self.env=old
                    if '←' in body:
                        return f'(← VeriPy.{name}Checked (fun {self.pattern(g.target)} => (do return {body})) (fun {self.pattern(g.target)} => {model}) {seq})'
                    return f'({seq}).{name} (fun {self.pattern(g.target)} => {body})'
            if isinstance(n.func,ast.Attribute):
                if isinstance(n.func.value,ast.Name) and n.func.value.id=='math' and n.func.attr=='prod' and len(n.args)==1:return '('+self.expr(n.args[0])+').prod'
                v=self.expr(n.func.value)
                if n.func.attr in ('index','find') and len(n.args)==1 and not n.keywords and self.typ(n.func.value)==S and self.typ(n.args[0])==S:
                    needle=self.expr(n.args[0])
                    if self.spec or n.func.attr=='find':return f'(VeriPy.stringFind {v} {needle})'
                    return f'(← VeriPy.stringIndex {v} {needle})'
                if n.func.attr=='split' and len(n.args)==1 and isinstance(n.args[0],ast.Constant) and type(n.args[0].value)is str and len(n.args[0].value)==1:
                    return f'(({v}).splitOn ({ord(n.args[0].value)} : Nat))'
                if n.func.attr=='count' and len(n.args)==1:
                    if isinstance(n.args[0],ast.Constant) and isinstance(n.args[0].value,str) and len(n.args[0].value)==1:
                        return f'(Int.ofNat (({v}).count ({ord(n.args[0].value)} : Nat)))'
                if n.func.attr in ('endswith','startswith') and len(n.args)==1 and self.typ(n.func.value)==S and self.typ(n.args[0])==S:
                    method='isSuffixOf' if n.func.attr=='endswith' else 'isPrefixOf'
                    return f'(({self.expr(n.args[0])}).{method} {v})'
        if isinstance(n,(ast.ListComp,ast.GeneratorExp)):
            if len(n.generators)!=1:fail(n,'nested comprehension pending')
            g=n.generators[0];old=self.env.copy();old_nonnegative=self.nonnegative.copy()
            seq=self.iter_expr(g.iter)
            self.bind_type(g.target,self.iter_type(g.iter))
            if isinstance(g.iter,ast.Call) and isinstance(g.iter.func,ast.Name) and g.iter.func.id=='range' and isinstance(g.target,ast.Name):
                lo=g.iter.args[0] if len(g.iter.args)>1 else ast.Constant(0)
                if self.is_nonnegative(lo):self.nonnegative.add(g.target.id)
            body=self.expr(n.elt);body_type=self.typ(n.elt);conds=[self.prop(x) for x in g.ifs]
            mode=self.spec;self.spec=True;model=self.expr(n.elt);self.spec=mode
            self.env=old;self.nonnegative=old_nonnegative
            if '←' in body or any('←' in c for c in conds):
                if any('←' in c for c in conds):fail(n,'effectful comprehension filters are not yet supported')
                if conds:seq=f'({seq}).filter (fun {self.pattern(g.target)} => decide ({" ∧ ".join(conds)}))'
                return f'(← VeriPy.mapChecked (fun {self.pattern(g.target)} => (do return {body} : Except VeriPy.Error {body_type.lean()})) (fun {self.pattern(g.target)} => {model}) ({seq}))'
            seq=self.iter_expr(g.iter)
            if conds:seq=f'({seq}).filter (fun {self.pattern(g.target)} => decide ({" ∧ ".join(conds)}))'
            return f'(({seq}).map (fun {self.pattern(g.target)} => {body}))'
        fail(n,'unsupported Lean imperative expression '+ast.dump(n))
    def sort_key(self,n):
        if isinstance(n,ast.Tuple):
            chunks=[]
            for item in n.elts:
                if isinstance(item,ast.Starred):
                    if self.typ(item.value)!=Ty('list',(I,)):fail(item,'expanded sort keys must contain integers')
                    chunks.append(self.expr(item.value))
                else:
                    if self.typ(item)!=I:fail(item,'sort keys must contain integers')
                    chunks.append('['+self.expr(item)+']')
            return '('+' ++ '.join(chunks)+')' if chunks else '([] : List Int)'
        if self.typ(n)!=I:fail(n,'sort keys must be integers or integer tuples')
        return '['+self.expr(n)+']'
    def ordered(self,t,a,b):
        if t==I:return a+' ≤ '+b
        if t.kind=='tuple':
            parts=[]
            for i,kind in enumerate(t.args):
                projection='.2'*i+('' if i==len(t.args)-1 else '.1')
                x='('+a+')'+projection;y='('+b+')'+projection
                if kind!=I:fail(self.module,'sorting currently requires integer tuple elements')
                parts.append((x,y))
            result=parts[-1][0]+' ≤ '+parts[-1][1]
            for x,y in reversed(parts[:-1]):result=x+' < '+y+' ∨ ('+x+' = '+y+' ∧ ('+result+'))'
            return result
        fail(self.module,'unsupported sorting element type')
    def is_nonnegative(self,n):
        return (isinstance(n,ast.Constant) and type(n.value)is int and n.value>=0) or (isinstance(n,ast.Name) and n.id in self.nonnegative)
    def pattern(self,n):
        if isinstance(n,ast.Name):return ident(n.id)
        if isinstance(n,ast.Tuple):return '('+', '.join(self.pattern(x) for x in n.elts)+')'
        fail(n,'unsupported binder')
    def error_value(self,name):
        if name=='ValueError':return 'VeriPy.Error.value'
        return '(VeriPy.Error.custom '+str(sorted(self.exceptions).index(name)+2)+')'
    def matches_error(self,value,name,node):
        if name=='Exception':return 'True'
        if name not in {'ValueError',*self.exceptions}:fail(node,'handler requires a modeled exception class')
        values=[]
        for cls in ['ValueError',*sorted(self.exceptions)]:
            ancestor=cls
            while True:
                if ancestor==name:
                    values.append(value+' = '+self.error_value(cls));break
                if ancestor not in self.exceptions:break
                ancestor=self.exceptions[ancestor]
        return '('+' ∨ '.join(values)+')'
    def exception_try(self,n,indent):
        # A result-valued region keeps failed assignments from committing. This
        # deliberately excludes mutation, local-state recovery and finally.
        if n.finalbody or n.orelse or len(n.handlers)!=1 or len(n.body)!=1:
            fail(n,'Lean modeled try requires one expression statement and one handler, without else/finally')
        handler=n.handlers[0]
        if handler.name or not isinstance(handler.type,ast.Name):fail(handler,'handler requires an unbound modeled exception class')
        condition=self.matches_error('__vp_caught',handler.type.id,handler)
        statement=n.body[0]
        assignment=isinstance(statement,ast.Assign) and len(statement.targets)==1 and isinstance(statement.targets[0],ast.Name)
        returning=isinstance(statement,ast.Return) and statement.value is not None
        if not (assignment or returning):fail(statement,'Lean modeled try supports a single name assignment or return expression')
        if len(handler.body)!=1 or not isinstance(handler.body[0],ast.Raise if assignment else (ast.Return,ast.Raise)):
            fail(handler,'assignment handlers must raise; return handlers must return or raise')
        t=self.typ(statement.value)
        prefix=' '*indent
        target=statement.targets[0].id if assignment else None
        if assignment and target in self.env:fail(statement,'try assignment must introduce a fresh local')
        opening=('let mut '+ident(target)+' : '+t.lean()+' ← ' if assignment else 'return ← ')
        self.emit(prefix+opening+'(do',n.lineno)
        self.emit(prefix+'  try',n.lineno)
        self.emit(prefix+'    pure '+self.expr(statement.value),statement.lineno)
        self.emit(prefix+'  catch __vp_caught =>',handler.lineno)
        self.emit(prefix+'    if '+condition+' then',handler.lineno)
        if isinstance(handler.body[0],ast.Return):
            self.emit(prefix+'      pure '+self.expr(handler.body[0].value),handler.body[0].lineno)
        else:
            self.block(handler.body,indent+6)
            self.emit(prefix+'      pure (default : '+t.lean()+')')
        self.emit(prefix+'    else',handler.lineno)
        self.emit(prefix+'      VeriPy.raise __vp_caught',handler.lineno)
        self.emit(prefix+'  : Except VeriPy.Error '+t.lean()+')')
        if assignment:
            self.env[target]=t;self.capture_models[target]=None;self.nonnegative.discard(target)
    def loop_errors(self):
        clauses=self.clauses('ensures')+self.clauses('ghost_ensures')
        if not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='raised' for e,_ in clauses for n in ast.walk(e)):return 'False'
        args=' '.join(ident('__vp_old_'+name if name in self.mutparams else name) for name in self.params)
        return '('+ident(self.fn_spec.name+'__error')+' '+args+' __vp_error)'
    def clauses(self,kind):
        return [(ast.parse(c.desugared or c.raw,mode='eval').body,c.line) for c in self.fn_spec.by_kind(kind)]
    def conjunction(self,clauses):return '('+' ∧ '.join(self.prop(n) for n,_ in clauses)+')' if clauses else 'True'
    def block(self,stmts,indent=2):
        for n in stmts:
            prefix=' '*indent
            if isinstance(n,ast.Expr) and isinstance(n.value,ast.Constant) and isinstance(n.value.value,str):continue
            if isinstance(n,(ast.Assign,ast.AnnAssign)):
                target=n.target if isinstance(n,ast.AnnAssign) else n.targets[0]
                if isinstance(target,ast.Subscript):
                    if not isinstance(target.value,ast.Name):fail(n,'nested mutation unsupported')
                    primitive='set' if self.is_nonnegative(target.slice) else 'setPython'
                    name=ident(target.value.id);self.emit(prefix+f'{name} ← VeriPy.{primitive} {name} {self.expr(target.slice)} {self.expr(n.value)}',n.lineno);continue
                t=annotation(n.annotation) if isinstance(n,ast.AnnAssign) else self.typ(n.value)
                e=self.expr(n.value)
                mode=self.spec;self.spec=True
                try:
                    model=None if any(isinstance(x,ast.Call) and isinstance(x.func,ast.Name) and x.func.id in self.fns for x in ast.walk(n.value)) else self.expr(n.value)
                finally:self.spec=mode
                if isinstance(target,ast.Name):
                    name=target.id
                    if name in self.env:
                        if self.env[name].kind=='opt' and t==self.env[name].args[0]:
                            e='some '+e;model='some '+model if model is not None else None;t=self.env[name]
                        self.emit(prefix+f'{ident(name)} := {e}',n.lineno)
                    else:self.emit(prefix+f'let mut {ident(name)} : {t.lean()} := {e}',n.lineno)
                    self.env[name]=t
                    self.capture_models[name]=model
                    self.nonnegative.discard(name)
                elif isinstance(target,ast.Tuple) and t.kind=='tuple' and len(target.elts)==len(t.args) and all(isinstance(x,ast.Name) for x in target.elts):
                    temporary='__vp_tuple_'+str(n.lineno)
                    self.emit(prefix+'let '+ident(temporary)+' := '+e,n.lineno)
                    for index,(item,kind) in enumerate(zip(target.elts,t.args)):
                        value=ident(temporary)+'.2'*index+('' if index==len(t.args)-1 else '.1')
                        self.emit(prefix+(ident(item.id)+' := ' if item.id in self.env else 'let mut '+ident(item.id)+' : '+kind.lean()+' := ')+value,n.lineno)
                        self.env[item.id]=kind;self.nonnegative.discard(item.id)
                else:fail(n,'unsupported tuple assignment')
            elif isinstance(n,ast.AugAssign):
                if isinstance(n.target,ast.Subscript):
                    target=n.target
                    if not isinstance(n.op,ast.Mult) or not isinstance(target.value,ast.Name) or not isinstance(target.slice,(ast.Name,ast.Constant)) or self.typ(target.value)!=Ty('list',(I,)) or self.typ(n.value)!=I or any(isinstance(x,(ast.Call,ast.NamedExpr)) for x in ast.walk(n.value)):
                        fail(n,'element *= requires an integer list, simple index and call-free integer RHS')
                    stem='__vp_aug_'+str(n.lineno);name=ident(target.value.id)
                    self.emit(prefix+'let '+stem+'_index := '+self.expr(target.slice),n.lineno)
                    self.emit(prefix+'let '+stem+'_old ← VeriPy.getPython '+name+' '+stem+'_index',n.lineno)
                    self.emit(prefix+'let '+stem+'_rhs := '+self.expr(n.value),n.lineno)
                    self.emit(prefix+name+' ← VeriPy.setPython '+name+' '+stem+'_index ('+stem+'_old * '+stem+'_rhs)',n.lineno)
                    self.capture_models[target.value.id]=None
                    continue
                if not isinstance(n.target,ast.Name):fail(n,'only scalar augmented assignment')
                value=n.value
                if self.env.get(n.target.id)==I and isinstance(n.op,ast.Add) and isinstance(value,(ast.Name,ast.Constant)) and self.typ(value)==B:
                    value=ast.IfExp(test=value,body=ast.Constant(value=1),orelse=ast.Constant(value=0))
                e=ast.BinOp(n.target,n.op,value);self.emit(prefix+f'{ident(n.target.id)} := {self.expr(e)}',n.lineno);self.nonnegative.discard(n.target.id)
            elif isinstance(n,ast.Delete):
                if len(n.targets)!=1 or not isinstance(n.targets[0],ast.Subscript) or not isinstance(n.targets[0].value,ast.Name):fail(n,'only contiguous local list slice deletion is supported')
                target=n.targets[0];sl=target.slice;name=target.value.id
                if not isinstance(sl,ast.Slice) or sl.lower is not None or sl.upper is None or sl.step is not None:fail(n,'only prefix slice deletion is supported')
                cutoff=self.expr(sl.upper)
                self.emit(prefix+ident(name)+' := '+ident(name)+'.drop (if '+cutoff+' < 0 then max 0 (Int.ofNat '+ident(name)+'.length + '+cutoff+') else '+cutoff+').toNat',n.lineno)
            elif isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Name) and n.value.func.id=='insort':
                call=n.value
                if len(call.args)!=2 or call.keywords or not isinstance(call.args[0],ast.Name):fail(n,'insort requires a local list and one value')
                name=call.args[0].id;t=self.env[name].args[0];value=self.expr(call.args[1])
                self.emit(prefix+ident(name)+' := VeriPy.insort (fun a b => decide ('+self.ordered(t,'a','b')+')) '+ident(name)+' '+value,n.lineno)
            elif isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and n.value.func.attr=='sort':
                call=n.value
                if not isinstance(call.func.value,ast.Name) or call.args or call.keywords:fail(n,'only in-place natural list sorting is supported')
                name=call.func.value.id;t=self.env[name]
                if t.kind!='list':fail(n,'sort requires a list')
                compare=' (fun a b => decide ('+self.ordered(t.args[0],'a','b')+'))'
                self.emit(prefix+ident(name)+' := '+ident(name)+'.mergeSort'+compare,n.lineno)
                previous=self.capture_models.get(name)
                self.capture_models[name]='('+previous+').mergeSort'+compare if previous is not None else None
            elif isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and n.value.func.attr=='append':
                call=n.value
                if not isinstance(call.func.value,ast.Name) or len(call.args)!=1 or call.keywords:fail(n,'unsupported append')
                name=call.func.value.id
                if self.env[name].kind!='list':fail(n,'append requires a list')
                self.emit(prefix+f'{ident(name)} := {ident(name)} ++ [{self.expr(call.args[0])}]',n.lineno)
            elif isinstance(n,ast.Return):
                if self.result_type==U:
                    if n.value is not None and not (isinstance(n.value,ast.Constant) and n.value.value is None):fail(n,'unit return requires None')
                    value='()'
                else:
                    value=self.expr(n.value)
                    if self.result_type.kind=='opt' and self.typ(n.value)==self.result_type.args[0]:value='some '+value
                self.emit(prefix+'return '+value,n.lineno)
            elif isinstance(n,ast.If):
                before=self.env.copy();at=len(self.lines)
                self.emit(prefix+'if '+self.prop(n.test)+' then',n.lineno);self.block(n.body,indent+2)
                then_env=self.env.copy();self.env=before.copy()
                if n.orelse:self.emit(prefix+'else');self.block(n.orelse,indent+2)
                else_env=self.env.copy()
                common={k:t for k,t in then_env.items() if k not in before and else_env.get(k)==t}
                if common:
                    declarations=[prefix+'let mut '+ident(k)+' : '+t.lean()+' := default' for k,t in common.items()]
                    for j in range(at,len(self.lines)):
                        for k,t in common.items():self.lines[j]=self.lines[j].replace('let mut '+ident(k)+' : '+t.lean()+' := ',ident(k)+' := ')
                    self.lines[at:at]=declarations
                    self.line_map={k+len(declarations) if k>at else k:v for k,v in self.line_map.items()}
                    for k in common:self.capture_models[k]=None
                self.env={**before,**common}
            elif isinstance(n,ast.For):
                if n.orelse:fail(n,'for else unsupported')
                invs=[(x,line) for x,line in self.clauses('invariant') if n.lineno<line<n.body[0].lineno]
                if not invs:fail(n,'Lean imperative loop requires head invariants')
                def has_break(statements):
                    for statement in statements:
                        if isinstance(statement,ast.Break):return True
                        if isinstance(statement,(ast.For,ast.While,ast.AsyncFor,ast.FunctionDef)):continue
                        children=list(ast.iter_child_nodes(statement))
                        if has_break(children):return True
                    return False
                manual=self.fn_spec.name+'__proof' in getattr(self.proof_lemmas,'theorems',())
                broken='__vp_broke_'+str(n.lineno) if has_break(n.body) and (not manual or getattr(n,'_veripy_peeled',False)) else None
                if broken:
                    self.emit(prefix+'let mut '+ident(broken)+' : Bool := false')
                    self.env[broken]=B;self.capture_models[broken]='false'
                enumerable=isinstance(n.iter,ast.Call) and isinstance(n.iter.func,ast.Name) and n.iter.func.id=='enumerate'
                seq=n.iter.args[0] if enumerable else n.iter
                t=self.typ(seq).args[0];old=self.env.copy();old_origins=self.loop_origins.copy();old_models=self.capture_models.copy();index='__vp_index_'+str(n.lineno)
                self.emit(prefix+f'let mut {ident(index)} : Int := 0')
                self.env[index]=I
                target=n.target.elts[1] if enumerable else n.target
                if any(isinstance(x,ast.Name) and x.id in old for x in ast.walk(n.target)):fail(n,'loop target rebinding an existing local is not admitted yet')
                self.emit(prefix+'for '+self.pattern(target)+' in VeriPy.loopTag '+str(n.lineno)+' ('+self.expr(seq)+') do',n.lineno)
                self.bind_type(target,t)
                if isinstance(target,ast.Name):self.loop_origins[target.id]=(n.lineno,0,0,0)
                elif isinstance(target,ast.Tuple):
                    for j,item in enumerate(target.elts):
                        if isinstance(item,ast.Name):self.loop_origins[item.id]=(n.lineno,0,j,len(target.elts))
                ranged=isinstance(seq,ast.Call) and isinstance(seq.func,ast.Name) and seq.func.id=='range' and isinstance(target,ast.Name)
                if ranged:
                    lo=seq.args[0] if len(seq.args)>1 else ast.Constant(0)
                    if self.is_nonnegative(lo):self.nonnegative.add(target.id)
                if enumerable:
                    idx=n.target.elts[0];self.loop_origins[idx.id]=(n.lineno,1,0,0);self.env[idx.id]=I;self.nonnegative.add(idx.id);self.emit(prefix+'  let '+ident(idx.id)+' := '+ident(index))
                assigned={x.id for a in ast.walk(n) for x in ([a.target] if isinstance(a,(ast.AugAssign,ast.AnnAssign)) else a.targets if isinstance(a,ast.Assign) else []) if isinstance(x,ast.Name)}
                assigned|={a.targets[0].value.id for a in ast.walk(n) if isinstance(a,ast.Assign) and isinstance(a.targets[0],ast.Subscript) and isinstance(a.targets[0].value,ast.Name)}
                assigned|={a.func.value.id for a in ast.walk(n) if isinstance(a,ast.Call) and isinstance(a.func,ast.Attribute) and a.func.attr=='append' and isinstance(a.func.value,ast.Name)}
                assigned|={a.targets[0].value.id for a in ast.walk(n) if isinstance(a,ast.Delete) and isinstance(a.targets[0],ast.Subscript) and isinstance(a.targets[0].value,ast.Name)}
                assigned|={a.args[0].id for a in ast.walk(n) if isinstance(a,ast.Call) and isinstance(a.func,ast.Name) and a.func.id=='insort' and a.args and isinstance(a.args[0],ast.Name)}
                for binder in ast.walk(target):
                    if isinstance(binder,ast.Name) and binder.id in assigned:
                        self.emit(prefix+'  let mut '+ident(binder.id)+' := '+ident(binder.id))
                if broken:assigned.add(broken)
                mutated=[k for k in old if k in assigned]+[index]
                self.spec=True;self.loop_index=ident(index);ren=self.renames.copy()
                if enumerable:self.renames[n.target.elts[0].id]=ident(index)
                elif ranged:self.renames[target.id]='('+self.expr(lo)+' + '+ident(index)+')'
                invname=self.fn_spec.name+'__inv_'+str(n.lineno)
                invvars={**self.inv_params,**old,**{k:self.env[k] for k in mutated}}
                signature=' '.join('('+ident(k)+' : '+t.lean()+')' for k,t in invvars.items())
                self.invariant_defs.append(('def '+ident(invname)+' '+signature+' : Prop := '+self.conjunction(invs),invs[0][1]))
                cursor_fact=f'{ident(index)} = Int.ofNat __vp_cursor.prefix.length'
                if broken:
                    cursor_fact='(('+ident(broken)+' = false ∧ '+cursor_fact+') ∨ ('+ident(broken)+' = true ∧ 0 < '+ident(index)+' ∧ __vp_cursor.suffix = []))'
                formula='('+ident(invname)+' '+' '.join(ident(k) for k in invvars)+') ∧ '+cursor_fact
                invariant='⇓⟨__vp_cursor, '+', '.join(ident(k) for k in mutated)+'⟩ => ⌜'+formula+'⌝'
                errors=self.loop_errors()
                if errors!='False':
                    invariant='(fun ⟨__vp_cursor, '+', '.join(ident(k) for k in mutated)+'⟩ => ⌜'+formula+'⌝, fun __vp_error => ⌜'+errors+'⌝, ())'
                if any(isinstance(x,ast.Return) for stmt in n.body for x in ast.walk(stmt)):
                    state=ident(mutated[0]) if len(mutated)==1 else '('+', '.join(ident(k) for k in mutated)+')'
                    post=ident(self.fn_spec.name+'__post')+' '+' '.join(ident('__vp_old_'+k if k in self.mutparams else k) for k in self.params)+' __vp_return'
                    invariant='Invariant.withEarlyReturnNewDo (onReturn := fun __vp_return _ => ⌜'+post+'⌝) (onContinue := fun __vp_cursor '+state+' => ⌜'+formula+'⌝) (onExcept := ⟨fun _ => ⌜False⌝, ()⟩)'
                self.invariant_tags.append(n.lineno)
                self.invariants.append((invariant,invs[0][1],[(k,self.capture_models.get(k),invvars[k].lean(),self.loop_origins.get(k)) for k in invvars if (k not in self.params or k in self.mutparams) and k not in mutated]))
                self.renames=ren;self.spec=False
                self.emit(prefix+'  '+ident(index)+' := '+ident(index)+' + 1')
                self.break_flags.append(broken)
                self.block(n.body,indent+2);self.break_flags.pop();self.env=old;self.loop_origins=old_origins;self.nonnegative.intersection_update(old)
                # Body expressions can mention binders that cease to exist here.
                # Prefer the actual contextual value; retain only the entry model
                # as a fallback for a branch that skips this loop entirely.
                for k in mutated:
                    if k in old:self.capture_models[k]=old_models.get(k)
            elif isinstance(n,ast.While):
                if n.orelse:fail(n,'while else pending')
                invs=[(x,line) for x,line in self.clauses('invariant') if n.lineno<line<n.body[0].lineno]
                decreases=[(x,line) for x,line in self.clauses('decreases') if n.lineno<line<n.body[0].lineno]
                if not invs or len(decreases)!=1:fail(n,'while requires head invariants and one decreasing measure')
                old=self.env.copy()
                assigned={x.id for stmt in ast.walk(n) if isinstance(stmt,(ast.Assign,ast.AnnAssign,ast.AugAssign)) for target in (stmt.targets if isinstance(stmt,ast.Assign) else [stmt.target]) for x in ast.walk(target) if isinstance(x,ast.Name) and isinstance(x.ctx,ast.Store)}
                mutated=[k for k in old if k in assigned]
                self.spec=True
                invname=self.fn_spec.name+'__inv_'+str(n.lineno)
                invvars={**self.inv_params,**old}
                signature=' '.join('('+ident(k)+' : '+t.lean()+')' for k,t in invvars.items())
                self.invariant_defs.append(('def '+ident(invname)+' '+signature+' : Prop := '+self.conjunction(invs),invs[0][1]))
                state=ident(mutated[0]) if len(mutated)==1 else '('+', '.join(ident(k) for k in mutated)+')'
                if not mutated:fail(n,'while without mutable state is unsupported')
                formula='('+ident(invname)+' '+' '.join(ident(k) for k in invvars)+')'
                condition=self.prop(n.test)
                measure=self.expr(decreases[0][0])
                captures=[(k,self.capture_models.get(k),invvars[k].lean(),self.loop_origins.get(k)) for k in invvars if (k not in self.params or k in self.mutparams) and k not in mutated]
                early=any(isinstance(x,ast.Return) for stmt in n.body for x in ast.walk(stmt))
                measure_state='(_, '+state+')' if early else state
                self.invariant_tags.extend([None,None])
                self.invariants.append(('fun '+measure_state+' => ⟨('+measure+').toNat⟩',decreases[0][1],captures))
                if early:
                    args=' '.join(ident('__vp_old_'+k if k in self.mutparams else k) for k in self.params)
                    post=ident(self.fn_spec.name+'__post')+' '+args+' __vp_return'
                    invariant='(fun __vp_state => match __vp_state with | .inl (__vp_returned, '+state+') => ⌜__vp_returned = none ∧ '+formula+'⌝ | .inr (some __vp_return, _) => ⌜'+post+'⌝ | .inr (none, '+state+') => ⌜'+formula+' ∧ ¬ '+condition+'⌝, fun _ => ⌜False⌝, ())'
                else:
                    invariant='(fun __vp_state => match __vp_state with | .inl '+state+' => ⌜'+formula+'⌝ | .inr '+state+' => ⌜'+formula+' ∧ ¬ '+condition+'⌝, fun _ => ⌜False⌝, ())'
                self.invariants.append((invariant,invs[0][1],captures))
                self.spec=False
                self.emit(prefix+'while '+self.prop(n.test)+' do',n.lineno)
                self.break_flags.append(None)
                self.block(n.body,indent+2);self.break_flags.pop();self.env=old
            elif isinstance(n,ast.Continue):self.emit(prefix+'continue',n.lineno)
            elif isinstance(n,ast.Try):
                if self.exceptions:
                    self.exception_try(n,indent)
                    continue
                if n.finalbody or len(n.handlers)!=1 or n.handlers[0].name is not None or not isinstance(n.handlers[0].type,ast.Name) or n.handlers[0].type.id!='ValueError':fail(n,'unsupported exception handler')
                handler=n.handlers[0].body
                if len(handler)!=1 or not isinstance(handler[0],ast.Raise) or not isinstance(handler[0].exc,ast.Call) or not isinstance(handler[0].exc.func,ast.Name) or handler[0].exc.func.id!='ValueError':fail(n,'only ValueError rethrow handlers are admitted here')
                # In the exception-class model a ValueError-to-ValueError rethrow
                # preserves the outcome. Checked accesses still propagate their
                # distinct exceptions, and else executes only after success.
                self.block(n.body,indent)
                self.block(n.orelse,indent)
            elif isinstance(n,ast.Break):
                if self.break_flags and self.break_flags[-1]:
                    self.emit(prefix+ident(self.break_flags[-1])+' := true',n.lineno)
                self.emit(prefix+'break',n.lineno)
            elif isinstance(n,ast.Raise):
                if not isinstance(n.exc,ast.Call) or not isinstance(n.exc.func,ast.Name) or n.exc.func.id not in {'ValueError',*self.exceptions}:fail(n,'raise requires a modeled exception class')
                # Python evaluates exception arguments before constructing and
                # raising the exception. Preserve checked reads/divisions in
                # f-string fields even though messages are outside our model.
                for arg in n.exc.args:
                    if isinstance(arg,ast.BinOp) and isinstance(arg.op,ast.Mod):
                        from veripy.frontend.exception_format import percent_char_operand
                        try: operand=percent_char_operand(arg)
                        except ValueError as exc: fail(arg,str(exc))
                        if self.typ(operand)!=S:fail(arg,'exception %c operand requires a builtin string')
                        temporary='__vp_format_'+str(n.lineno)
                        self.emit(prefix+'let '+temporary+' := '+self.expr(operand),n.lineno)
                        self.emit(prefix+'if '+temporary+'.length ≠ 1 then',n.lineno)
                        self.emit(prefix+'  let _ ← VeriPy.raise (α := Unit) VeriPy.Error.type',n.lineno)
                        continue
                    if isinstance(arg,ast.JoinedStr) and any(
                        isinstance(x,ast.FormattedValue) and (x.format_spec is not None or x.conversion not in (-1,114))
                        for x in arg.values
                    ):
                        fail(arg,'exception f-string formatting and conversions are outside the Lean model')
                    values=[x.value for x in arg.values if isinstance(x,ast.FormattedValue)] if isinstance(arg,ast.JoinedStr) else [arg]
                    for value in values:
                        # Admission permits repr(list(xs)) for list[int] error
                        # payloads. The discarded shallow copy has the same
                        # value; preserve evaluation of xs before the raise.
                        if (isinstance(value,ast.Call) and isinstance(value.func,ast.Name)
                                and value.func.id=='list' and len(value.args)==1 and not value.keywords
                                and self.typ(value.args[0])==Ty('list',(I,))):
                            value=value.args[0]
                        self.emit(prefix+'let _ := '+self.expr(value),n.lineno)
                self.emit(prefix+'let _ ← VeriPy.raise (α := Unit) '+self.error_value(n.exc.func.id),n.lineno)
            else:fail(n,'unsupported Lean imperative statement '+type(n).__name__)
    def compile(self):
        for name,fields in self.fields.items():
            self.emit('structure '+ident(name)+' where')
            for f,t in fields.items():self.emit('  '+ident(f)+' : '+t.lean())
            self.emit('  deriving Repr, Inhabited, DecidableEq')
        self.emit('-- VERIPY MODEL PRELUDE')
        proofs=[]
        for spec in self.specs.functions:
            scopes=getattr(self.proof_lemmas,'scopes',{})
            self.proof_hints=frozenset(x for x in getattr(self.proof_lemmas,'theorems',self.proof_lemmas) if not scopes.get(x) or spec.name in scopes[x])
            self.fn_spec=spec;fn=self.fns[spec.name];self.env={a.arg:annotation(a.annotation) for a in [*fn.args.args,*fn.args.kwonlyargs]};self.renames={};self.result_type=annotation(fn.returns);self.invariants=[];self.invariant_defs=[];self.invariant_tags=[];self.loop_origins={};self.nonnegative=set();self.capture_models={}
            self.shadowed={n.id for n in ast.walk(fn) if isinstance(n,ast.Name) and isinstance(n.ctx,(ast.Store,ast.Del))} | set(self.env)
            self.pure_guards=any(isinstance(n,ast.Name) and n.id.startswith('__vp_fixed_active_') for n in ast.walk(fn))
            params=self.env.copy();self.params=params;binders=' '.join('('+ident(n)+' : '+t.lean()+')' for n,t in params.items());args=' '.join(ident(n) for n in params)
            self.mutparams={x.id for stmt in ast.walk(fn) if isinstance(stmt,(ast.Assign,ast.AnnAssign,ast.AugAssign)) for target in (stmt.targets if isinstance(stmt,ast.Assign) else [stmt.target]) for x in ast.walk(target) if isinstance(x,ast.Name) and isinstance(x.ctx,ast.Store) and x.id in params}
            self.inv_params={('__vp_old_'+k if k in self.mutparams else k):v for k,v in params.items()}
            self.emit(f'def {ident(fn.name)} {binders} : Except VeriPy.Error {self.result_type.lean()} := do',fn.lineno)
            for k in params:
                if k in self.mutparams:
                    self.emit('  let '+ident('__vp_old_'+k)+' := '+ident(k))
                    self.emit('  let mut '+ident(k)+' := '+ident(k))
                    self.renames['old:'+k]=ident('__vp_old_'+k)
            self.block(fn.body)
            if self.result_type!=U and isinstance(fn.body[-1],ast.Raise):
                # The preceding throw cannot return. Supply the result type of
                # the enclosing do block without changing its error outcome.
                self.emit('  return (default : '+self.result_type.lean()+')',fn.end_lineno)
            if self.result_type==U:self.emit('  return ()',fn.end_lineno)
            for definition,line in self.invariant_defs:self.emit(definition,line)
            self.env=params;self.spec=True;self.renames={'result':'__vp_result','raised':'False'}
            reqs=self.clauses('requires');posts=self.conjunction((self.clauses('ensures')+self.clauses('ghost_ensures')))
            premises=' '.join(f'(__vp_h{k} : {self.prop(e)})' for k,(e,_) in enumerate(reqs))
            self.renames={'result':'(default : '+self.result_type.lean()+')','raised':'True'};errors=self.conjunction((self.clauses('ensures')+self.clauses('ghost_ensures'))) if any(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='raised' for e,_ in (self.clauses('ensures')+self.clauses('ghost_ensures')) for n in ast.walk(e)) else 'False'
            if errors!='False' and not self.exceptions:errors='(__vp_error = VeriPy.Error.value ∧ '+errors+')'
            errorname=fn.name+'__error'
            self.emit('def '+ident(errorname)+' '+binders+' (__vp_error : VeriPy.Error) : Prop := '+errors)
            errors='('+ident(errorname)+' '+args+' __vp_error)'
            postname=fn.name+'__post'
            self.emit('def '+ident(postname)+' '+binders+' (__vp_result : '+self.result_type.lean()+') : Prop := '+posts)
            proof_start=len(self.lines)
            posts='('+ident(postname)+' '+args+' __vp_result)'
            theorem=fn.name+'_spec';self.theorems.append(theorem)
            self.emit(f'@[spec] theorem {ident(theorem)} {binders} {premises} :\n  ⦃⌜True⌝⦄ {ident(fn.name)} {args} ⦃(fun __vp_result => ⌜{posts}⌝, fun (__vp_error : VeriPy.Error) => ⌜{errors}⌝, ())⦄ := by',spec.lineno)
            self.emit(f'  mvcgen [{ident(fn.name)}, '+('VeriPy.decimal, ' if any(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='int' for n in ast.walk(fn)) else '')+f'VeriPy.requireSome, VeriPy.maximum, VeriPy.setPython, VeriPy.getPython, VeriPy.set, VeriPy.get, VeriPy.divmod, VeriPy.div, VeriPy.mod]',spec.lineno)
            for invariant_index,(inv,line,captures) in enumerate(self.invariants,1):
                capture_parts=[]
                for k,model,ty,origin in captures:
                    if k.startswith('__vp_old_'):
                        capture_parts.append('let '+ident(k)+' := '+ident(k[len('__vp_old_'):]))
                        continue
                    choices=['veripy_capture '+ident(k)]
                    if origin:choices.append('veripy_cursor '+ident(k)+' '+' '.join(map(str,origin)))
                    if model is not None:choices.append('veripy_let '+ident(k)+' := '+model)
                    choices.append('veripy_capture_type '+ident(k)+' : '+ty)
                    capture_parts.append('(first | '+' | '.join(choices)+')')
                capture='; '.join(capture_parts)
                if self.invariant_tags[invariant_index-1] is not None:
                    self.emit('  all_goals try (veripy_loop_tag '+str(self.invariant_tags[invariant_index-1])+'; exact (by '+(capture+'; ' if capture else '')+'exact '+inv+'))',line)
                elif len(self.invariants)==1:
                    self.emit('  all_goals try (exact (by '+(capture+'; ' if capture else '')+'exact '+inv+'))',line)
                else:
                    self.emit('  case inv'+str(invariant_index)+' => exact (by '+(capture+'; ' if capture else '')+'exact '+inv+')',line)
            hints=', '.join([*(ident(x) for x in sorted(self.proof_hints)), *(ident(f.name+suffix) for f in self.specs.functions if any(isinstance(c,ast.Call) and isinstance(c.func,ast.Name) and c.func.id==f.name for c in ast.walk(fn)) for suffix in ('__post','__error')), *(ident(fn.name+'__inv_'+str(c.lineno)) for c in ast.walk(fn) if isinstance(c,(ast.For,ast.While)))])
            scoped_hints=', '.join([*(ident(x) for x in sorted(self.proof_hints) if spec.name in scopes.get(x,())), *(ident(fn.name+'__inv_'+str(c.lineno)) for c in ast.walk(fn) if isinstance(c,(ast.For,ast.While)))])
            helper_defs=[ident(f.name+suffix) for f in self.specs.functions if any(isinstance(c,ast.Call) and isinstance(c.func,ast.Name) and c.func.id==f.name for c in ast.walk(fn)) for suffix in ('__post','__error')]
            branches=' '.join('| (solve | apply '+ident(x)+' <;> first | assumption | rfl | (solve | simp_all only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, if_true, if_false]) | (solve | simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero] at * <;> omega) | omega)' for x in sorted(self.proof_hints))
            self.emit("""  all_goals (
    try veripy_clear_aux
    try (simp only [VeriPy.loopTag, decide_eq_true_eq, WhileVariant.eval, SVal.evalsTo_nil, ULift.up.injEq, reduceCtorEq, Option.some.injEq, true_and, and_true, false_or, exists_eq_left, SPred.and_nil, SPred.or_nil, SPred.exists_nil, SPred.down_pure_nil, List.cons_ne_nil, and_false, false_and, exists_false, or_false, Int.toNat_natCast, List.length_mergeSort, List.length_append, List.length_cons, List.length_nil] at *)
    try (repeat' veripy_split_cursor)
    try (repeat' veripy_split_goal)
    all_goals try veripy_continue_facts
    all_goals try veripy_project_facts
    all_goals try (dsimp (config := { zetaDelta := true }) only at *)
    all_goals try veripy_fold_projections
    all_goals try (simp only [VeriPy.ofNat_cast, Int.natCast_add, Int.natCast_one, Int.natCast_zero, Int.not_ofNat_neg, if_false, Int.toNat_natCast] at *)
    all_goals first | assumption | exact ExceptConds.entails_false | exact ExceptConds.entails.rfl | omega """+branches+(" | (exfalso; first "+branches+")" if branches else "")+" | grind ["+ident(postname)+", "+ident(errorname)+"] | grind (lax := true) ["+(scoped_hints+", " if scoped_hints else "")+ident(postname)+", "+ident(errorname)+"] | grind (lax := true) ["+(hints+", " if hints else "")+ident(postname)+", "+ident(errorname)+"]\n  )",spec.lineno)
            full_proof=fn.name+'__proof'
            if full_proof in getattr(self.proof_lemmas,'theorems',()):
                # A manually directed proof must inhabit the exact generated
                # triple. Lean checks both this application and its full axiom
                # closure; it cannot replace the model or weaken the contract.
                body_start=proof_start+2
                del self.lines[body_start:]
                self.line_map={k:v for k,v in self.line_map.items() if k<=body_start}
                self.emit('  exact '+ident(full_proof)+' '+args+' '+' '.join('__vp_h'+str(k) for k in range(len(reqs))),spec.lineno)
            self.emit('#print axioms '+ident(theorem))
            proof_lines=self.lines[proof_start:]
            proof_map={k-proof_start:v for k,v in self.line_map.items() if k>proof_start}
            proofs.append((proof_lines,proof_map))
            del self.lines[proof_start:]
            self.line_map={k:v for k,v in self.line_map.items() if k<=proof_start}
            self.spec=False
        self.emit('-- VERIPY IMPERATIVE PROOF SUPPORT')
        for lines,mapping in proofs:
            offset=len(self.lines);self.lines.extend(lines)
            self.line_map.update({offset+k:v for k,v in mapping.items()})
        from veripy.backends.lean.encoder import LeanEncoded
        return LeanEncoded('\n'.join(self.lines)+'\n',self.line_map,self.theorems)


def encode_imperative(source,specs,module_name,proof_lemmas=frozenset()):
    module=ast.parse(source)
    for n in ast.walk(module):
        name=n.id if isinstance(n,ast.Name) else n.arg if isinstance(n,ast.arg) else ''
        if name.startswith('__vp_'):fail(n,'reserved Lean imperative implementation prefix')
    # Preserve the established Python admission/alias/spec-placement boundary.
    # This is only encoding, never a request for or reuse of a Dafny proof.
    from veripy.backends.dafny.encoder import ProofSymbols
    ghost_names=set()
    for function in specs.functions:
        for clause in function.clauses:
            try: expression=ast.parse(clause.desugared or clause.raw,mode='eval')
            except SyntaxError: continue
            for node in ast.walk(expression):
                if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id=='ghost' and node.args and isinstance(node.args[0],ast.Constant) and node.args[0].value in proof_lemmas:
                    ghost_names.add(node.args[0].value)
    admission_symbols=ProofSymbols(proof_lemmas,ghost_names)
    has_outcomes=any(isinstance(n,ast.Raise) for n in ast.walk(module)) or any(c.kind=='ensures' and 'raised(' in (c.desugared or c.raw) for f in specs.functions for c in f.clauses)
    if has_outcomes:
        from veripy.backends.dafny.outcomes import encode_outcomes
        encode_outcomes(source,specs,module_name,admission_symbols)
    else:
        from veripy.backends.dafny.encoder import encode_module
        encode_module(source,specs,module_name,admission_symbols)
    return Compiler(source,specs,proof_lemmas).compile()
