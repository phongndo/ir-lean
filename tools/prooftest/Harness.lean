/-! What `tools/prooftest/prooftest.py` runs in Lean for a tier-1 proof test. It writes `import Lean`, `import IRLean`,
the generated module and an `open` above this text, and runs it as a server: one request per line on stdin, and one
answer per line on stdout, each starting with `IRLEAN_PROOFTEST` and the run's nonce, so nothing else Lean prints can
pass for an answer.

The statement comes from the JSON file `IRLEAN_PROOFTEST_CONFIG` names, so nothing in a request is pasted into Lean
source. It's elaborated where only Lean, IRLean and the generated module are imported, as `tools/verify.py` elaborates
a pinned statement, so evaluating it runs no code but theirs.

Two things happen here:

- **Search.** The statement becomes one function from the inputs, as natural numbers, to `1` when the conclusion
  holds, `2` when it doesn't, and otherwise which hypothesis is false: `0` for the first, and `2 + k` for hypothesis
  `k` after it. It's compiled once, and then run on each input. That trusts Lean's compiler, as `native_decide`
  does.
- **Confirmation.** For a failing input, this builds a theorem `¬ statement` and has the kernel check it. Every
  emitted function runs its blocks through `IRLean.run`, a `partial_fixpoint` the kernel can't unfold. So each call of
  a generated function in the instance is rewritten to `runFuel`, which the kernel can, with `run_eq_runFuel`, which
  needs the run to finish within its fuel. -/

open Lean Meta Elab Command

/- Deciding an `Outcome` needs this, as in tools/verify_check.lean. -/
deriving instance DecidableEq for Except

namespace IRLeanProoftest

open IRLean

/-- `IRLean.run` with fuel: `none` when the fuel runs out, as when the run never ends. The kernel can evaluate this. -/
def runFuel {β ρ : Type} (step : β → Outcome (Next β ρ)) : Nat → β → Outcome ρ
  | 0, _ => none
  | n + 1, b =>
    match step b with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (.ret r)) => some (.ok r)
    | some (.ok (.jump b')) => runFuel step n b'

/-- A run that finishes within its fuel is the run. -/
theorem run_eq_runFuel {β ρ : Type} (step : β → Outcome (Next β ρ)) (n : Nat) (b : β)
    (h : (runFuel step n b).isSome = true) : run step b = runFuel step n b := by
  induction n generalizing b with
  | zero => simp [runFuel] at h
  | succ n ih =>
    rw [run]
    simp only [runFuel] at h ⊢
    cases hs : step b with
    | none => simp [hs] at h
    | some x =>
      cases x with
      | error e => rfl
      | ok nx =>
        cases nx with
        | ret r => rfl
        | jump b' =>
          simp only [hs] at h
          exact ih b' h

/-- A run under a promise to progress that finishes within its fuel is the run: the promise only says what a run
that never finishes does. -/
theorem promised_run_eq_runFuel {β ρ : Type} (step : β → Outcome (Next β ρ)) (n : Nat) (b : β)
    (d : Unit → Outcome ρ) (h : (runFuel step n b).isSome = true) : promised (run step b) d = runFuel step n b := by
  rw [run_eq_runFuel step n b h]
  cases hr : runFuel step n b with
  | none => rw [hr] at h; cases h
  | some x => rfl

/-! ### Results stated as `∃ r, f x = Outcome.ok (some r) ∧ q r`

Lean decides an `∃` over `BitVec 64` by trying every value, which never ends. The equation pins `r`, so these decide
it by running the call once. -/

/-- Whether `e` returns `some a` with `q a`. -/
def okSomeThen {α : Type} (e : Outcome (Option α)) (q : α → Prop) [DecidablePred q] : Bool :=
  match e with
  | some (.ok (some a)) => decide (q a)
  | _ => false

theorem okSomeThen_iff {α : Type} (e : Outcome (Option α)) (q : α → Prop) [DecidablePred q] :
    okSomeThen e q = true ↔ ∃ r, e = Outcome.ok (some r) ∧ q r := by
  cases e with
  | none => simp [okSomeThen, Outcome.ok]
  | some x =>
    cases x with
    | error s => simp [okSomeThen, Outcome.ok]
    | ok v =>
      cases v with
      | none => simp [okSomeThen, Outcome.ok]
      | some a => simp [okSomeThen, Outcome.ok]

theorem not_of_okSomeThen {α : Type} {e : Outcome (Option α)} {q : α → Prop} [DecidablePred q]
    (h : okSomeThen e q = false) : ¬ ∃ r, e = Outcome.ok (some r) ∧ q r := fun hc => by
  rw [(okSomeThen_iff e q).mpr hc] at h
  cases h

theorem not_of_okSome {α : Type} {e : Outcome (Option α)} (h : okSomeThen e (fun _ => True) = false) :
    ¬ ∃ r, e = Outcome.ok (some r) := fun ⟨r, hr⟩ => not_of_okSomeThen h ⟨r, hr, trivial⟩

/-- `(e, q, bare)` when `c` is `∃ r, e = Outcome.ok (some r) ∧ q r`, or `∃ r, e = Outcome.ok (some r)` with `bare`
set and `q` true, where `e` doesn't mention `r`. -/
def okSomePattern? (c : Expr) : Option (Expr × Expr × Bool) := do
  guard (c.isAppOfArity ``Exists 2)
  let .lam n ty body bi := c.appArg! | none
  let (eqn, rest, bare) :=
    if body.isAppOfArity ``And 2 then (body.appFn!.appArg!, body.appArg!, false)
    else (body, mkConst ``True, true)
  guard (eqn.isAppOfArity ``Eq 3)
  let lhs := eqn.appFn!.appArg!
  let rhs := eqn.appArg!
  guard (rhs.isAppOfArity ``IRLean.Outcome.ok 2)
  guard (rhs.appArg!.isAppOfArity ``Option.some 2 && rhs.appArg!.appArg! == .bvar 0)
  guard !lhs.hasLooseBVars
  return (lhs, .lam n ty rest bi, bare)

/-! ### Inputs

An input is an `Array Nat`, one entry for each binder that isn't a hypothesis, in order. A buffer's entry is where
its bytes are in the same array instead: its length there, then a byte to an entry. So a property with memory is
still one array, and the search, the kernel and the store take it the same way. -/

def bitvecOf (w n : Nat) : BitVec w := BitVec.ofNat w n

/-- A value of `Val w`: `2 ^ w` and above stand for poison. -/
def valOf (w n : Nat) : Option (BitVec w) := if n < 2 ^ w then some (BitVec.ofNat w n) else none

def boolOf (n : Nat) : Bool := n != 0

/-- The bytes of the buffer whose entry is `slot`: its length at `args[args[slot]]`, and its bytes after it. -/
def bytesOf (args : Array Nat) (slot : Nat) (n : Nat) : List Nat :=
  let start := args.getD slot 0
  (List.range (min (args.getD start 0) n)).map fun i => args.getD (start + 1 + i) 0

def bufferOf (n : Nat) (args : Array Nat) (slot : Nat) : IRLean.Ptf.Buffer n :=
  IRLean.Ptf.Buffer.ofList n ((bytesOf args slot n).map (BitVec.ofNat 8))

/-- The binders tier 1 can generate values for. A pointer is into a buffer, and a length is of a pointer: `of` is
the binder it depends on, by its place among the binders. -/
inductive Kind where
  | bitvec (w : Nat)
  | val (w : Nat)
  | bool
  | buffer (max : Nat)
  | pointer (of : Nat)
  | length (of : Nat)
  deriving Inhabited

structure Binder where
  name : String
  kind : Kind
  type : String

def Kind.json : Kind → List (String × Json)
  | .bitvec w => [("kind", "bitvec"), ("width", toJson w)]
  | .val w => [("kind", "val"), ("width", toJson w)]
  | .bool => [("kind", "bool")]
  | .buffer n => [("kind", "buffer"), ("max", toJson n)]
  | .pointer i => [("kind", "pointer"), ("of", toJson i)]
  | .length i => [("kind", "length"), ("of", toJson i)]

/-- A reason for an answer that isn't a verdict, and its detail. -/
abbrev M := ExceptT (String × String) MetaM

def refuse (reason : String) (detail : MessageData) : M α := do
  throwThe (String × String) (reason, ← detail.toString)

/-- Runs `x`, and returns its exception instead of throwing it. -/
def attempt [Monad m] [MonadExcept Exception m] (x : m α) : m (Except Exception α) := do
  try return .ok (← x) catch e => return .error e

/-- Runs `x`, and refuses with `reason` if it throws. -/
def orRefuse (x : MetaM α) (reason : String) (detail : MessageData) : M α := do
  match ← (attempt x : MetaM _) with
  | .ok a => return a
  | .error _ => refuse reason detail

def widthOf? (ty : Expr) : MetaM (Option Nat) := do
  let ty ← whnfR ty
  unless ty.isAppOfArity ``BitVec 1 do return none
  evalNat (← instantiateMVars ty.appArg!) |>.run

/-- The kind of a binder of type `ty`. `earlier` are the binders before it, as the terms that stand for them in `ty`,
with their kinds, so a pointer can say which buffer it's into. -/
def kindOf? (ty : Expr) (earlier : Array (Expr × Kind)) : MetaM (Option Kind) := do
  if let some w ← widthOf? ty then return some (.bitvec w)
  let ty' ← whnfR ty
  if ty'.isAppOfArity ``Option 1 then
    if let some w ← widthOf? ty'.appArg! then return some (.val w)
  if ty'.isConstOf ``Bool then return some .bool
  let ty ← instantiateMVars ty
  let dependsOn (e : Expr) (ok : Kind → Bool) : Option Nat :=
    earlier.findIdx? fun (x, k) => x == e && ok k
  if ty.isAppOfArity ``IRLean.Ptf.Buffer 1 then
    if let some n ← (evalNat ty.appArg!).run then return some (.buffer n)
  if ty.isAppOfArity ``IRLean.Ptf.Pointer 2 then
    if let some i := dependsOn ty.appArg! (fun | .buffer _ => true | _ => false) then return some (.pointer i)
  if ty.isAppOfArity ``IRLean.Ptf.Length 3 then
    if let some i := dependsOn ty.appArg! (fun | .pointer _ => true | _ => false) then return some (.length i)
  return none

/-- The value of a binder of kind `k`, from entry `i` of the input `args`. `earlier` stand for the binders before
it. -/
def valueOf (k : Kind) (args : Expr) (i : Nat) (earlier : Array Expr) : MetaM Expr := do
  let n := mkApp4 (mkConst ``Array.getD [Level.zero]) (mkConst ``Nat) args (mkNatLit i) (mkNatLit 0)
  match k with
  | .bitvec w => return mkApp2 (mkConst ``bitvecOf) (mkNatLit w) n
  | .val w => return mkApp2 (mkConst ``valOf) (mkNatLit w) n
  | .bool => return mkApp (mkConst ``boolOf) n
  | .buffer m => return mkApp3 (mkConst ``bufferOf) (mkNatLit m) args (mkNatLit i)
  | .pointer j => mkAppM ``IRLean.Ptf.Pointer.ofNat #[earlier[j]!, n]
  | .length j => mkAppM ``IRLean.Ptf.Length.ofNat #[earlier[j]!, n]

/-- The value of binder `i`, of type `ty`, from the input `values`, as a literal, which is how it's shown, and what
the kernel checks. A pointer's or a length's type names the literal it depends on. -/
def literalOf (k : Kind) (ty : Expr) (values : Array Nat) (i : Nat) : MetaM Expr := do
  let n := values.getD i 0
  match k with
  | .bitvec w => return mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit (n % 2 ^ w))
  | .val w =>
    let ty := mkApp (mkConst ``BitVec) (mkNatLit w)
    if n < 2 ^ w then mkSome ty (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit n))
    else return mkApp (mkConst ``Option.none [Level.zero]) ty
  | .bool => return mkConst (if n != 0 then ``Bool.true else ``Bool.false)
  | .buffer m =>
    let byte := mkApp (mkConst ``BitVec) (mkNatLit 8)
    let bytes := (bytesOf values i m).map fun b => mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit (b % 256))
    return mkApp2 (mkConst ``IRLean.Ptf.Buffer.ofList) (mkNatLit m) (← mkListLit byte bytes)
  | .pointer _ => mkAppM ``IRLean.Ptf.Pointer.ofNat #[(← instantiateMVars ty).appArg!, mkNatLit n]
  | .length _ => mkAppM ``IRLean.Ptf.Length.ofNat #[(← instantiateMVars ty).appArg!, mkNatLit n]

/-! ### Running on `ExecMem`

The statement is about `Mem`. To run it fast, the search rewrites each call of a generated function that takes
memory into a call of its copy on `ExecMem`, from `ir-lean --executable-memory`, with the memory it's given read as
the `ExecMem` it stands for, and the memory it gives back read back with `toMem`:

  `f args m`  becomes  `Outcome.map ExecMem.out (f' args x)`, where `x.toMem = m`

`x` is found for `Ptf.place m bufs`, which is `toMem` of `Ptf.placeExec x bufs` by `Ptf.toMem_placeExec`, for the
module's `initial` and other memory it defines, whose copies build the same memory by `ExecMem.toMem_empty`,
`toMem_addGlobal`, `toMem_addReloc` and `toMem_reserve`, for `Mem.empty`, by `toMem_empty`, and for `toMem x` itself.
A call whose memory isn't one of those runs on `Mem`, as it's written. That the copy then returns what `f` does is
`docs/memory.md#why-a-test-on-execmem-is-a-test-of-mem`: proved from block to whole run, and argued for each block.

Only the search runs this. The kernel and `tools/verify.py` confirm a counterexample on the statement as written. -/

/-- The generated module's namespace, and its copy's on `ExecMem`. -/
structure Copy where
  generated : Name
  exec : Name

def isMem (ty : Expr) : MetaM Bool := return (← whnfR ty).isConstOf ``IRLean.Mem

/-- The copy's constant for `c`, a constant of the generated module, if the copy has one. -/
def Copy.const? (copy : Copy) (c : Name) : MetaM (Option Name) := do
  unless copy.generated.isPrefixOf c do return none
  let c' := c.replacePrefix copy.generated copy.exec
  return if (← getEnv).contains c' then some c' else none

mutual
/-- `e`, a memory, as the `ExecMem` whose `toMem` it is, if it's one this knows. -/
partial def Copy.memory? (copy : Copy) (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOfArity ``IRLean.Ptf.place 2 then
    let some x ← copy.memory? e.appFn!.appArg! | return none
    return some (mkApp2 (mkConst ``IRLean.Ptf.placeExec) x e.appArg!)
  if e.isAppOfArity ``IRLean.ExecMem.toMem 1 then return some e.appArg!
  if e.isAppOfArity ``IRLean.Mem.empty 1 then return some (mkApp (mkConst ``IRLean.ExecMem.empty) e.appArg!)
  let .const c lvls := e.getAppFn | return none
  let some c' ← copy.const? c | return none
  let some args ← copy.arguments? e.getAppArgs | return none
  let x := mkAppN (mkConst c' lvls) args
  return if (← isDefEq (← inferType x) (mkConst ``IRLean.ExecMem)) then some x else none

/-- The arguments of a call, with each memory as its `ExecMem`. -/
partial def Copy.arguments? (copy : Copy) (args : Array Expr) : MetaM (Option (Array Expr)) := do
  let mut out := #[]
  for a in args do
    if ← isMem (← inferType a) then
      let some x ← copy.memory? a | return none
      out := out.push x
    else out := out.push a
  return some out
end

/-- `e`, a call of a generated function that takes memory, as a call of its copy with the result read back. `none`
if it isn't one, and `some none` if it is but its memory isn't one this knows. -/
def Copy.call? (copy : Copy) (e : Expr) : MetaM (Option (Option Expr)) := do
  let .const c lvls := e.getAppFn | return none
  let some c' ← copy.const? c | return none
  let args := e.getAppArgs
  let takesMemory ← args.anyM fun a => do isMem (← inferType a)
  unless takesMemory do return none
  let ty ← inferType e
  let some args' ← copy.arguments? args | return some none
  let call := mkAppN (mkConst c' lvls) args'
  -- `Outcome (α × ExecMem)`, read back with `ExecMem.out`, or `Outcome ExecMem`, with `toMem`.
  let ty' ← whnfR (← inferType call)
  unless ty'.isAppOfArity ``Option 1 && ty'.appArg!.isAppOfArity ``Except 2 do return some none
  let result := ty'.appArg!.appArg!
  let back ←
    if result.isAppOfArity ``Prod 2 && (← isDefEq result.appArg! (mkConst ``IRLean.ExecMem)) then
      mkAppOptM ``IRLean.ExecMem.out #[some result.appFn!.appArg!]
    else if ← isDefEq result (mkConst ``IRLean.ExecMem) then pure (mkConst ``IRLean.ExecMem.toMem)
    else return some none
  let read ← mkAppM ``IRLean.Outcome.map #[back, call]
  return if ← isDefEq (← inferType read) ty then some (some read) else some none

/-- `e` with every call of a generated function that takes memory run on `ExecMem` where the copy can. Counts calls
rewritten and calls left on `Mem` in `stats`. -/
def Copy.rewrite (copy : Copy) (stats : IO.Ref (Nat × Nat)) (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    match ← copy.call? e with
    | some (some e') => stats.modify (fun (a, b) => (a + 1, b)); return .done e'
    | some none => stats.modify (fun (a, b) => (a, b + 1)); return .done e
    | none => return .done e)

def u8 (n : UInt8) : Expr := toExpr n

/-- What the decision says when hypothesis `k`, counting from 0, is false: `0` for the first, as for any hypothesis
before this said which, and `2 + k` for each after it, so `1` and `2` stay the conclusion's. `255` for the 254th
and later. -/
def falseCode (k : Nat) : UInt8 := if k == 0 then 0 else (min (2 + k) 255).toUInt8

/-- What a decision is built from: the input, the generated module's copy on `ExecMem`, if there is one, and how
many calls of a function with memory it rewrote to run there, and how many it left on `Mem`. -/
structure Build where
  args : Expr
  copy : Option Copy
  stats : IO.Ref (Nat × Nat)

/-- A proposition as it's decided: on `ExecMem` where it can be. -/
def Build.prepare (b : Build) (p : Expr) : MetaM Expr := do
  match b.copy with
  | some copy => copy.rewrite b.stats (← zetaReduce (← instantiateMVars p))
  | none => return p

/-- The statement as one decision: `1` if the conclusion holds, `2` if it doesn't, and `falseCode k` if hypothesis
`k` is false, the first one that is. Each binder that isn't a hypothesis takes the next input, and `hyp` counts the
hypotheses so far. `earlier` stand for the binders so far, with their kinds. -/
partial def decision (build : Build) (e : Expr) (i hyp : Nat) (acc : Array Binder) (earlier : Array (Expr × Kind)) :
    M (Expr × Array Binder) := do
  match e with
  | .forallE n ty body bi =>
    if ← isProp ty then
      if body.hasLooseBVar 0 then
        refuse "statement_unsupported" m!"the statement uses the proof of hypothesis {n}, which can't be decided"
      let (rest, acc) ← decision build (body.lowerLooseBVars 1 1) i (hyp + 1) acc earlier
      let d ← orRefuse (do mkDecide (← build.prepare ty)) "undecidable" m!"Lean can't decide the hypothesis {ty}"
      return (← mkAppM ``cond #[d, rest, u8 (falseCode hyp)], acc)
    else if bi.isInstImplicit then
      let inst ← orRefuse (synthInstance ty) "statement_unsupported" m!"no instance of {ty}"
      decision build (body.instantiate1 inst) i hyp acc earlier
    else
      let some k ← kindOf? ty earlier
        | refuse "binder_unsupported" m!"{n} : {ty}. Tier 1 generates `BitVec w`, `IRLean.Val w`, `Bool`, \
            `IRLean.Ptf.Buffer n`, and a `IRLean.Ptf.Pointer` and a `IRLean.Ptf.Length` into a buffer it binds"
      let b : Binder := { name := n.eraseMacroScopes.toString, kind := k, type := toString (← ppExpr ty) }
      withLetDecl n ty (← valueOf k build.args i (earlier.map (·.1))) fun x => do
        let (rest, acc) ← decision build (body.instantiate1 x) (i + 1) hyp (acc.push b) (earlier.push (x, k))
        return (← mkLetFVars #[x] rest, acc)
  | c =>
    let c' ← build.prepare c
    let d ← match okSomePattern? c' with
      | some (call, q, _) =>
        orRefuse (mkAppOptM ``okSomeThen #[none, some call, some q, none]) "undecidable"
          m!"Lean can't decide the conclusion {c}"
      | none => orRefuse (mkDecide c') "undecidable" m!"Lean can't decide the conclusion {c}"
    return (← mkAppM ``cond #[d, u8 1, u8 2], acc)

/-- The statement with each binder that isn't a hypothesis replaced by its input. Hypotheses stay as implications,
as in tools/verify_check.lean, so the instance is false exactly when the input meets them and the conclusion fails. -/
partial def instantiateWith (e : Expr) (kinds : Array Kind) (values : Array Nat) (i : Nat) : M Expr := do
  match e with
  | .forallE n ty body bi =>
    if ← isProp ty then
      return .forallE n ty (← instantiateWith (body.lowerLooseBVars 1 1) kinds values i) bi
    else if bi.isInstImplicit then
      instantiateWith (body.instantiate1 (← synthInstance ty)) kinds values i
    else
      let some k := kinds[i]? | refuse "internal_error" m!"no binder {i}"
      instantiateWith (body.instantiate1 (← literalOf k ty values i)) kinds values (i + 1)
  | c => return c

/-- A proof that a closed conclusion is false: by `decide`, or for `∃ r, f x = Outcome.ok (some r) ∧ q r` by running
the call once. -/
def proofNot (c : Expr) : MetaM Expr := do
  match okSomePattern? c with
  | some (call, q, bare) =>
    let lhs ← mkAppOptM ``okSomeThen #[none, some call, some q, none]
    let h := mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.false)) (← mkEq lhs (mkConst ``Bool.false))
    mkAppM (if bare then ``not_of_okSome else ``not_of_okSomeThen) #[h]
  | none => mkDecideProof (mkNot c)

/-- A proof of `¬ p`, for a closed instance `p` whose hypotheses are implications: each hypothesis decided true, and
the conclusion false. -/
def proofNotInstance (p : Expr) : MetaM Expr := do
  let rec split : Expr → Array Expr × Expr
    | .forallE _ ty body _ => let (hs, c) := split body; (#[ty] ++ hs, c)
    | c => (#[], c)
  let (hypotheses, conclusion) := split p
  let proofs ← hypotheses.mapM mkDecideProof
  let notConclusion ← proofNot conclusion
  withLocalDeclD `f p fun f => do
    mkLambdaFVars #[f] (mkApp notConclusion (mkAppN f proofs))

/-- A proof of the instance from a proof `acc` of the statement. -/
partial def applyTo (e acc : Expr) (kinds : Array Kind) (values : Array Nat) (i : Nat) : MetaM Expr := do
  match e with
  | .forallE n ty body bi =>
    if ← isProp ty then
      let body := body.lowerLooseBVars 1 1
      withLocalDeclD n ty fun h => do
        mkLambdaFVars #[h] (← applyTo body (mkApp acc h) kinds values i)
    else if bi.isInstImplicit then
      let inst ← synthInstance ty
      applyTo (body.instantiate1 inst) (mkApp acc inst) kinds values i
    else
      let v ← literalOf kinds[i]! ty values i
      applyTo (body.instantiate1 v) (mkApp acc v) kinds values (i + 1)
  | _ => return acc

/-! ### Confirming in the kernel -/

/-- Calls `e` makes of the generated module's functions that name no bound variable, outermost first. -/
partial def callsIn (isGenerated : Name → Bool) (e : Expr) (acc : Array Expr) : Array Expr :=
  match e with
  | .forallE _ d b _ | .lam _ d b _ => callsIn isGenerated b (callsIn isGenerated d acc)
  | .letE _ t v b _ => callsIn isGenerated b (callsIn isGenerated v (callsIn isGenerated t acc))
  | .mdata _ b | .proj _ _ b => callsIn isGenerated b acc
  | .app .. =>
    match e.getAppFn with
    | .const c _ =>
      if isGenerated c && !e.hasLooseBVars then
        if acc.contains e then acc else acc.push e
      else e.getAppArgs.foldl (fun acc a => callsIn isGenerated a acc) acc
    | f => e.getAppArgs.foldl (fun acc a => callsIn isGenerated a acc) (callsIn isGenerated f acc)
  | _ => acc

def generatedCalls (generated : Name) (e : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let isGenerated (c : Name) : Bool :=
    match env.getModuleIdxFor? c with
    | some i => env.header.moduleNames[i.toNat]! == generated
    | none => false
  return callsIn isGenerated e #[]

/-- Checks `decl` with the kernel, and returns the environment with it. -/
def kernelAdd (decl : Declaration) (heartbeats : Nat) : MetaM Environment := do
  match (← getEnv).addDeclCore (heartbeats * 1000).toUSize 100000 decl none with
  | .ok env => return env
  | .error ex => throwError (ex.toMessageData {})

/-- A theorem `¬ statement`, from the input `values`, checked by the kernel. Returns its name, the instance it refutes,
and the axioms it rests on. -/
def refute (stmt : Expr) (generated : Name) (kinds : Array Kind) (values : Array Nat) (fuel heartbeats : Nat) :
    M (String × Array Name × Nat) := do
  let p ← instantiateWith stmt kinds values 0
  -- Each call that reaches `run`, under a promise or not, becomes `runFuel`, with a proof that the two are equal.
  let mut rewrites : Array (Expr × Expr × Expr) := #[]
  for call in ← generatedCalls generated p do
    -- A function under a promise to progress runs as `promised (run step b) d`, which a run that finishes is.
    let r ← whnfHeadPred call fun e => return !(e.isAppOf ``IRLean.run || e.isAppOf ``IRLean.promised)
    let promise := r.isAppOfArity ``IRLean.promised 3
    let inner := if promise then r.appFn!.appArg! else r
    unless inner.isAppOfArity ``IRLean.run 4 do continue
    let args := inner.getAppArgs
    let fueled := mkAppN (mkConst ``runFuel) #[args[0]!, args[1]!, args[2]!, mkNatLit fuel, args[3]!]
    let finished ← mkEq (← mkAppM ``Option.isSome #[fueled]) (mkConst ``Bool.true)
    let h := mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.true)) finished
    let eq :=
      if promise then
        mkAppN (mkConst ``promised_run_eq_runFuel)
          #[args[0]!, args[1]!, args[2]!, mkNatLit fuel, args[3]!, r.appArg!, h]
      else mkAppN (mkConst ``run_eq_runFuel) #[args[0]!, args[1]!, args[2]!, mkNatLit fuel, args[3]!, h]
    rewrites := rewrites.push (call, fueled, mkExpectedPropHint eq (← mkEq call fueled))
  -- ¬ p with every call replaced, by evaluation in the kernel, then back to ¬ p one call at a time.
  let mut steps : Array (Expr × Expr) := #[]
  let mut q := p
  for (call, fueled, eq) in rewrites do
    let abstracted ← kabstract q call
    let callType ← inferType call
    steps := steps.push (mkLambda `x .default callType (mkNot abstracted), eq)
    q := abstracted.instantiate1 fueled
  let mut proof ← proofNotInstance q
  for (motive, eq) in steps.reverse do
    proof ← mkEqNDRec motive proof (← mkEqSymm eq)
  let all ← withLocalDeclD `h stmt fun h => do
    mkLambdaFVars #[h] (mkApp proof (← applyTo stmt h kinds values 0))
  let name := `IRLeanProoftest.refuted
  let type := mkNot stmt
  let decl := Declaration.thmDecl { name, levelParams := [], type, value := all }
  let env ← match ← (attempt (kernelAdd decl heartbeats) : MetaM _) with
    | .ok env => pure env
    | .error ex => refuse "kernel_rejected" ex.toMessageData
  let axioms ← withEnv env (collectAxioms name)
  return (toString (← withOptions (·.setBool `pp.fullNames true) (ppExpr p)), axioms, rewrites.size)

/-! ### The server -/

structure Config where
  nonce : String
  statement : String
  generated : Name
  /-- The namespace of the generated module's copy on `ExecMem`, if `tools/prooftest/prooftest.py` made one. -/
  exec : Option Name
  fuel : Nat
  kernelHeartbeats : Nat
  /-- The process's own stdin and stdout. `#eval` gives its code an empty stdin, and keeps what it prints until it
  ends, which a server can't use. -/
  input : IO.FS.Handle
  output : IO.FS.Handle

def config : IO Config := do
  let some path ← IO.getEnv "IRLEAN_PROOFTEST_CONFIG"
    | throw (IO.userError "IRLEAN_PROOFTEST_CONFIG isn't set")
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let get {α} [FromJson α] (key : String) : IO α := IO.ofExcept (j.getObjValAs? α key)
  return {
    nonce := ← get "nonce"
    statement := ← get "statement"
    generated := (← get (α := String) "generated").toName
    exec := ((j.getObjValAs? String "exec").toOption).map String.toName
    fuel := ← get "fuel"
    kernelHeartbeats := ← get "kernel_heartbeats"
    input := ← IO.FS.Handle.mk "/dev/stdin" .read
    output := ← IO.FS.Handle.mk "/dev/stdout" .append }

def say (cfg : Config) (line : String) : IO Unit := do
  cfg.output.putStrLn s!"IRLEAN_PROOFTEST {cfg.nonce} {line}"
  cfg.output.flush

def answer (cfg : Config) (fields : List (String × Json)) : IO Unit :=
  say cfg (Json.mkObj fields).compress

def parseTerm (text : String) : TermElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `term text "<statement>" with
  | .ok s => return s
  | .error e => throwError "the statement doesn't parse: {e}"

def elabStatement (text : String) : TermElabM Expr := Term.withoutErrToSorry do
  let e ← Term.elabType (← parseTerm text)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "the statement has holes Lean couldn't fill"
  if e.hasSorry then throwError "the statement uses sorry"
  unless ← isProp e do throwError "the statement isn't a proposition"
  return e

def inputsOf (j : Json) : Except String (Array (Array Nat)) := do
  (← j.getObjValAs? (Array Json) "inputs").mapM fun i => do (← i.getArr?).mapM (·.getNat?)

def failure (cfg : Config) (reason detail : String) : IO Unit :=
  answer cfg [("kind", "failure"), ("reason", reason), ("detail", detail)]

/-- Evaluates inputs in order, saying each result as it comes, and stops at the first failure if asked. -/
def evalInputs (cfg : Config) (f : Array Nat → UInt8) (inputs : Array (Array Nat)) (stop : Bool) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut evaluated := 0
  for h : k in [0:inputs.size] do
    let r := f inputs[k]
    evaluated := k + 1
    say cfg s!"r {k} {r} {(← IO.monoNanosNow) - t0}"
    if stop && r == 2 then break
  answer cfg [("kind", "done"), ("evaluated", toJson evaluated), ("ns", toJson ((← IO.monoNanosNow) - t0))]

def kernel (cfg : Config) (stmt : Expr) (kinds : Array Kind) (values : Array Nat) : MetaM Unit := do
  let t0 ← IO.monoNanosNow
  let result ← (refute stmt cfg.generated kinds values cfg.fuel cfg.kernelHeartbeats).run
  let ns := (← IO.monoNanosNow) - t0
  match result with
  | .ok (inst, axioms, calls) =>
    answer cfg [("kind", "kernel"), ("ok", true), ("ns", toJson ns), ("instance", toJson inst),
      ("axioms", toJson (axioms.map toString)), ("calls_rewritten", toJson calls)]
  | .error (reason, detail) =>
    answer cfg [("kind", "kernel"), ("ok", false), ("ns", toJson ns), ("reason", toJson reason),
      ("detail", toJson detail)]

/-- Answers requests, one a line, until stdin closes or one says to quit. -/
partial def loop (cfg : Config) (stmt : Expr) (kinds : Array Kind) (f : Array Nat → UInt8) : MetaM Unit := do
  let line ← cfg.input.getLine
  if line.isEmpty then return
  let request ← match Json.parse line with
    | .ok j => pure j
    | .error e => throwError "bad request: {e}"
  match request.getObjValAs? String "op" with
  | .ok "eval" =>
    let inputs ← match inputsOf request with
      | .ok i => pure i
      | .error e => throwError "bad inputs: {e}"
    evalInputs cfg f inputs ((request.getObjValAs? Bool "stop").toOption.getD true)
    loop cfg stmt kinds f
  | .ok "kernel" =>
    let values ← match request.getObjValAs? (Array Nat) "input" with
      | .ok v => pure v
      | .error e => throwError "bad input: {e}"
    kernel cfg stmt kinds values
    loop cfg stmt kinds f
  | .ok "quit" => return
  | _ => throwError "unknown request: {line}"

/-- The decision for `stmt`, compiled, and its binders. -/
unsafe def compile (cfg : Config) (stmt : Expr) : M ((Array Nat → UInt8) × Array Binder × Nat × Nat) := do
  let arrayNat := mkApp (mkConst ``Array [Level.zero]) (mkConst ``Nat)
  let stats ← IO.mkRef (0, 0)
  let copy := cfg.exec.map fun exec => { generated := cfg.generated, exec }
  let (body, binders) ← withLocalDeclD `args arrayNat fun args => do
    let (body, binders) ← decision { args, copy, stats } stmt 0 0 #[] #[]
    return (← mkLambdaFVars #[args] body, binders)
  for c in body.getUsedConstants do
    if (← collectAxioms c).contains ``sorryAx then
      refuse "statement_invalid" m!"deciding it would use sorry, through {c}"
  let f ← orRefuse (evalExpr (Array Nat → UInt8) (← mkArrow arrayNat (mkConst ``UInt8)) body) "undecidable"
    m!"Lean couldn't compile the decision"
  let (onExec, onMem) ← stats.get
  return (f, binders, onExec, onMem)

unsafe def serve (cfg : Config) : TermElabM Unit := do
  let started ← IO.monoNanosNow
  match ← attempt (elabStatement cfg.statement) with
  | .error ex => failure cfg "statement_invalid" (← ex.toMessageData.toString)
  | .ok stmt =>
    match ← (compile cfg stmt).run with
    | .error (reason, detail) => failure cfg reason detail
    | .ok (f, binders, onExec, onMem) =>
      answer cfg [("kind", "ready"), ("ns", toJson ((← IO.monoNanosNow) - started)),
        ("statement", toJson (toString (← withOptions (·.setBool `pp.fullNames true) (ppExpr stmt)))),
        ("binders", toJson (binders.map fun b =>
          Json.mkObj ([("name", toJson b.name), ("type", toJson b.type)] ++ b.kind.json))),
        -- Calls of functions with memory the search runs on the copy on `ExecMem`, and on `Mem` as written.
        ("calls", Json.mkObj [("exec_memory", toJson onExec), ("mem", toJson onMem)])]
      loop cfg stmt (binders.map (·.kind)) f

set_option maxHeartbeats 0 in
#eval show CommandElabM Unit from do
  let cfg ← config
  try liftTermElabM (unsafe serve cfg)
  catch ex => failure cfg "internal_error" (← ex.toMessageData.toString)

end IRLeanProoftest
