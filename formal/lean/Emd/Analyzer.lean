import Emd.Bounded

/-! # `emd analyze`: a mirror of the abstract domain, and a checked result.

The fixed-point loop and the widening are not proved: `check` validates a recorded result, so what
they did does not matter. Soundness is scoped to the bounded machine: a run stops at the first
64-bit overflow, and the analyzer's report says that overflow on values it does not know exactly is
not analyzed. Relations are proved through an environment `σ` from symbols to integers, quantified
in the concretization, so no history is needed. -/

namespace Emd

namespace Analyzer

def maxValues : Nat := 512
def maxDepths : Nat := 32
def maxPairs : Nat := 8192
def maxAddresses : Nat := 16
def widenVisits : Nat := 1500
def widenSteps : Nat := 100000

/-! ## Values -/

inductive Val where
  | known (xs : List Int)
  | range (lo hi : Int)
  | unknown
  deriving DecidableEq

/-- `v` is one of the values described. -/
def Val.has : Val → Int → Prop
  | .known xs, v => v ∈ xs
  | .range lo hi, v => lo ≤ v ∧ v ≤ hi
  | .unknown, _ => True

def Val.one (v : Int) : Val := .known [v]

def Val.mkRange (lo hi : Int) : Val :=
  if lo = hi then .one lo
  else if lo = i64Min ∧ hi = i64Max then .unknown
  else .range lo hi

def listMin (xs : List Int) : Int := xs.foldr min i64Max

def listMax (xs : List Int) : Int := xs.foldr max i64Min

/-- A set past `maxValues` becomes the interval around it. -/
def Val.of (xs : List Int) : Val :=
  if xs.length > maxValues ∧ xs ≠ [] then .mkRange (listMin xs) (listMax xs) else .known xs

def Val.bounds : Val → Int × Int
  | .known xs => (listMin xs, listMax xs)
  | .range lo hi => (lo, hi)
  | .unknown => (i64Min, i64Max)

/-- Sorted insertion: the Rust's `BTreeSet`. -/
def insertS (x : Int) : List Int → List Int
  | [] => [x]
  | y :: l => if x < y then x :: y :: l else if x = y then y :: l else y :: insertS x l

def unionS (a b : List Int) : List Int := b.foldr insertS a

def Val.join (a b : Val) : Val :=
  match a, b with
  | .known x, .known y => if x = y then .known x else .of (unionS x y)
  | _, _ => .mkRange (min a.bounds.1 b.bounds.1) (max a.bounds.2 b.bounds.2)

def Val.contains : Val → Int → Bool
  | .known xs, v => xs.contains v
  | .range lo hi, v => decide (lo ≤ v) && decide (v ≤ hi)
  | .unknown, _ => true

def Val.single : Val → Option Int
  | .known [v] => some v
  | _ => none

inductive Cmp where
  | eq | ne | lt | ge | gt | le
  deriving DecidableEq

def Cmp.holds : Cmp → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => decide (a < b)
  | .ge, a, b => decide (a ≥ b)
  | .gt, a, b => decide (a > b)
  | .le, a, b => decide (a ≤ b)

def Cmp.negated : Cmp → Cmp
  | .eq => .ne
  | .ne => .eq
  | .lt => .ge
  | .ge => .lt
  | .gt => .le
  | .le => .gt

def checkedI (r : Int) : Option Int := if InI64 r then some r else none

def finishB (l h : Int) : Option Val := if l > h then none else some (.mkRange l h)

def restrictB (lo hi : Int) (c : Cmp) (b : Int) : Option Val :=
  match c with
  | .eq => finishB (max lo b) (min hi b)
  | .ne =>
    finishB (if lo = b then min (lo + 1) i64Max else lo) (if hi = b then max (hi - 1) i64Min else hi)
  | .lt => (checkedI (b - 1)).bind fun b' => finishB lo (min hi b')
  | .le => finishB lo (min hi b)
  | .gt => (checkedI (b + 1)).bind fun b' => finishB (max lo b') hi
  | .ge => finishB (max lo b) hi

/-- The values that satisfy `cmp` against `b`. `none` if there are none. -/
def Val.restrict (a : Val) (c : Cmp) (b : Int) : Option Val :=
  match a with
  | .known xs =>
    match xs.filter (fun x => c.holds x b) with
    | [] => none
    | kept => some (.of kept)
  | _ => restrictB a.bounds.1 a.bounds.2 c b

/-- Bounds that moved go to no bound at all. -/
def Val.widenedFrom (a before : Val) : Val :=
  .mkRange (if a.bounds.1 < before.bounds.1 then i64Min else a.bounds.1)
    (if a.bounds.2 > before.bounds.2 then i64Max else a.bounds.2)

/-! ## Relations and frames -/

/-- What a value is, in terms of a symbol named by the `pc` of an instruction. -/
inductive Rel where
  | offset (sym : Nat) (off : Int)
  | test (sym : Nat) (off : Int) (c : Cmp) (k : Int)
  deriving DecidableEq

def Rel.sym : Rel → Nat
  | .offset s _ => s
  | .test s _ _ _ => s

structure Cell where
  val : Val
  rel : Option Rel
  deriving DecidableEq

def Cell.plain (v : Val) : Cell := ⟨v, none⟩

def Cell.join (a b : Cell) : Cell :=
  ⟨a.val.join b.val, if a.rel = b.rel then a.rel else none⟩

/-- The top of the stack is the head of the list, as in the model. Memory is sorted by address. -/
structure Frame where
  stack : List Cell
  mem : List (Int × Cell)
  rest : Val
  deriving DecidableEq

def memGet (l : List (Int × Cell)) (a : Int) : Option Cell :=
  (l.find? fun e => e.1 == a).map (·.2)

def insertAt (k : Int) (c : Cell) : List (Int × Cell) → List (Int × Cell)
  | [] => [(k, c)]
  | e :: l => if k < e.1 then (k, c) :: e :: l else e :: insertAt k c l

def memSet (k : Int) (c : Cell) (l : List (Int × Cell)) : List (Int × Cell) :=
  insertAt k c (l.filter fun e => e.1 != k)

def Frame.start : Frame := ⟨[], [], .one 0⟩

def Frame.cellVal (f : Frame) (a : Int) : Val :=
  match memGet f.mem a with
  | some c => c.val
  | none => f.rest

def Frame.cellOf (f : Frame) (a : Int) : Cell :=
  (memGet f.mem a).getD (.plain f.rest)

def forgetCell (sym : Nat) (c : Cell) : Cell :=
  match c.rel with
  | some r => if r.sym = sym then ⟨c.val, none⟩ else c
  | none => c

def Frame.forget (f : Frame) (sym : Nat) : Frame :=
  { f with stack := f.stack.map (forgetCell sym), mem := f.mem.map fun e => (e.1, forgetCell sym e.2) }

def narrowCell (sym : Nat) (c : Cmp) (b : Int) (cell : Cell) : Option Cell :=
  match cell.rel with
  | some (.offset s off) =>
    if s = sym ∧ InI64 (b + off) then
      (cell.val.restrict c (b + off)).map fun v => { cell with val := v }
    else some cell
  | _ => some cell

def narrowStack (sym : Nat) (c : Cmp) (b : Int) : List Cell → Option (List Cell)
  | [] => some []
  | x :: l => do
    let x' ← narrowCell sym c b x
    let l' ← narrowStack sym c b l
    pure (x' :: l')

def narrowMem (sym : Nat) (c : Cmp) (b : Int) : List (Int × Cell) → Option (List (Int × Cell))
  | [] => some []
  | e :: l => do
    let x' ← narrowCell sym c b e.2
    let l' ← narrowMem sym c b l
    pure ((e.1, x') :: l')

def Frame.narrow (f : Frame) (sym : Nat) (c : Cmp) (b : Int) : Option Frame := do
  let st ← narrowStack sym c b f.stack
  let m ← narrowMem sym c b f.mem
  pure { f with stack := st, mem := m }

/-- `f` when the condition in `cond` was zero, or was not. -/
def Frame.afterBranch (f : Frame) (cond : Cell) (zero : Bool) : Option Frame :=
  match cond.rel with
  | some (.offset sym off) =>
    if InI64 (-off) then f.narrow sym (if zero then .eq else .ne) (-off) else some f
  | some (.test sym off c k) =>
    if InI64 (k - off) then f.narrow sym (if zero then c.negated else c) (k - off) else some f
  | none => some f

/-! ## One step -/

inductive Kind where
  | stackUnderflow | pcOutOfRange | divisionByZero | negativeAddress | invalidByte | overflow
  | unknownJump
  deriving DecidableEq

structure Step where
  next : List (Nat × Option Frame)
  issues : List (Kind × Bool)
  wild : Bool
  halts : Bool

def Step.empty : Step := ⟨[], [], false, false⟩

def Step.seq (a b : Step) : Step :=
  ⟨a.next ++ b.next, a.issues ++ b.issues, a.wild || b.wild, a.halts || b.halts⟩

def Step.issue (k : Kind) (certain : Bool) : Step := ⟨[], [(k, certain)], false, false⟩

/-- All pairs, in order: `f` on each, sorted, and whether any failed. -/
def pairsOut (f : Int → Int → Option Int) (xs ys : List Int) : List Int × Bool :=
  xs.foldl (fun acc x =>
    ys.foldl (fun acc y =>
      match f x y with
      | some v => (insertS v acc.1, acc.2)
      | none => (acc.1, true)) acc) ([], false)

def lift2 (a b : Val) (f : Int → Int → Option Int) : Option (Option Val × Bool) :=
  match a, b with
  | .known xs, .known ys =>
    if xs.length * ys.length > maxPairs then none
    else
      let r := pairsOut f xs ys
      some (if r.1 = [] then none else some (.of r.1), r.2)
  | _, _ => none

def boundAdd (x y none' : Int) : Int :=
  if x = none' ∨ y = none' then none' else
    match checkedI (x + y) with
    | some v => v
    | none => none'

def onBounds (i : Instr) (a b : Val) : Val :=
  let al := a.bounds.1
  let ah := a.bounds.2
  let bl := b.bounds.1
  let bh := b.bounds.2
  let either : Val := .known [0, 1]
  let verdict (yes : Bool) : Val := .one (if yes then 1 else 0)
  match i with
  | .add => .mkRange (boundAdd al bl i64Min) (boundAdd ah bh i64Max)
  | .sub =>
    if InI64 (-bl) ∧ InI64 (-bh) then
      .mkRange (boundAdd al (-bh) i64Min) (boundAdd ah (-bl) i64Max)
    else .unknown
  | .eq => if ah < bl ∨ bh < al then verdict false else either
  | .lt => if ah < bl then verdict true else if al ≥ bh then verdict false else either
  | .gt => if al > bh then verdict true else if ah ≤ bl then verdict false else either
  | .mod =>
    if bl ≠ i64Min ∧ bh ≠ i64Max then
      let top : Int := min ((max bl.natAbs bh.natAbs - 1 : Nat) : Int) i64Max
      if al ≥ 0 then .mkRange 0 top else .mkRange (-top) top
    else .unknown
  | _ => .unknown

/-- Reports values that are not allowed. The flag: can execution go on past this instruction. -/
def checkVal (k : Kind) (value : Val) (allowed : Int → Bool) : Step × Bool :=
  match value with
  | .known xs =>
    let good := (xs.filter allowed).length
    ((if good < xs.length then .issue k (good == 0) else .empty), decide (good > 0))
  | _ =>
    let lo := value.bounds.1
    let hi := value.bounds.2
    let fine := if k = .divisionByZero then decide (lo > 0) || decide (hi < 0)
      else allowed lo && allowed hi
    ((if fine then .empty else .issue k false), true)

def boundedAddresses (v : Val) : Val :=
  match v with
  | .known xs => if xs.length > maxAddresses then .mkRange (listMin xs) (listMax xs) else v
  | _ => v

def offsetPlus (c : Cell) (k : Int) : Option Rel :=
  match c.rel with
  | some (.offset s off) => (checkedI (off + k)).map fun o => .offset s o
  | _ => none

def offsetMinus (c : Cell) (k : Int) : Option Rel :=
  match c.rel with
  | some (.offset s off) => (checkedI (off - k)).map fun o => .offset s o
  | _ => none

def testOf (c : Cell) (cmp : Cmp) (k : Int) : Option Rel :=
  match c.rel with
  | some (.offset s off) => some (.test s off cmp k)
  | _ => none

/-- What `ADD` and `SUB` by a constant, and a comparison with one, keep of a relation. -/
def relate (i : Instr) (a b : Cell) : Option Rel :=
  match i with
  | .add =>
    match b.val.single, a.val.single with
    | some k, _ => offsetPlus a k
    | none, some k => offsetPlus b k
    | none, none => none
  | .sub =>
    match b.val.single with
    | some k => offsetMinus a k
    | none => none
  | .eq =>
    match b.val.single, a.val.single with
    | some k, _ => testOf a .eq k
    | none, some k => testOf b .eq k
    | none, none => none
  | .lt =>
    match b.val.single, a.val.single with
    | some k, _ => testOf a .lt k
    | none, some k => testOf b .gt k
    | none, none => none
  | .gt =>
    match b.val.single, a.val.single with
    | some k, _ => testOf a .gt k
    | none, some k => testOf b .lt k
    | none, none => none
  | _ => none

def withTop (rest : Option Frame) (top : List Cell) : Option Frame :=
  rest.map fun r => { r with stack := top ++ r.stack }

def land (P : List Instr) (t : Int) (after : Option Frame) : Step :=
  if 0 ≤ t ∧ t < (P.length : Int) then ⟨[(t.toNat, after)], [], false, false⟩
  else .issue .pcOutOfRange false

def jumpS (P : List Instr) (pc : Nat) (off : Val) (after : Option Frame) : Step :=
  match off with
  | .known xs => xs.foldl (fun acc o => acc.seq (land P ((pc : Int) + o) after)) .empty
  | _ => ⟨[], [(.unknownJump, false)], true, false⟩

def retS (P : List Instr) (addr : Val) (after : Option Frame) : Step :=
  match addr with
  | .known xs => xs.foldl (fun acc a => acc.seq (land P a after)) .empty
  | _ => ⟨[], [(.unknownJump, false)], true, false⟩

def binFn : Instr → Int → Int → Option Int
  | .add, a, b => checkedI (a + b)
  | .sub, a, b => checkedI (a - b)
  | .mul, a, b => checkedI (a * b)
  | .eq, a, b => some (b2i (a = b))
  | .lt, a, b => some (b2i (a < b))
  | .gt, a, b => some (b2i (a > b))
  | .div, a, b => checkedI (Int.tdiv a b)
  | .mod, a, b => some (Int.tmod a b)
  | _, _, _ => none

def resultOf (i : Instr) (a b : Val) : Option Val × Bool :=
  match lift2 a b (binFn i) with
  | some r => r
  | none => (some (onBounds i a b), false)

/-- `Dup` and `Over`: a copy with no relation gets a symbol. -/
def copyS (P : List Instr) (pc : Nat) (rest : Option Frame) (source : Cell)
    (between : Option Cell) : Step :=
  let fresh := source.rel = none
  let after := if fresh then rest.map (·.forget pc) else rest
  let shared : Cell := if fresh then ⟨source.val, some (.offset pc 0)⟩ else source
  let mid := if fresh then between.map (forgetCell pc) else between
  let top := match mid with
    | some c => [shared, c, shared]
    | none => [shared, shared]
  land P ((pc : Int) + 1) (withTop after top)

def loadFold (f : Frame) (xs : List Int) : Val :=
  ((xs.filter (0 ≤ ·)).foldl (fun acc a =>
    match acc with
    | none => some (f.cellVal a)
    | some x => some (x.join (f.cellVal a))) none).getD .unknown

def inInterval (lo hi k : Int) : Bool := decide (max lo 0 ≤ k) && decide (k ≤ max hi 0)

def loadS (f : Frame) (pc : Nat) (addr : Val) : Frame :=
  match boundedAddresses addr with
  | .known [a] =>
    let cell := f.cellOf a
    if cell.rel = none then
      let g := f.forget pc
      let c : Cell := ⟨cell.val, some (.offset pc 0)⟩
      { g with mem := memSet a c g.mem, stack := c :: g.stack }
    else { f with stack := cell :: f.stack }
  | .known xs => { f with stack := Cell.plain (loadFold f xs) :: f.stack }
  | other =>
    let lo := other.bounds.1
    let hi := other.bounds.2
    let inside := f.mem.filter fun e => inInterval lo hi e.1
    { f with stack := Cell.plain (inside.foldl (fun x e => x.join e.2.val) f.rest) :: f.stack }

def storeFold (f : Frame) (w : Cell) : List Int → List (Int × Cell) → List (Int × Cell)
  | [], m => m
  | a :: l, m =>
    let old := (memGet m a).getD (.plain f.rest)
    storeFold f w l (memSet a (old.join w) m)

def storeS (f : Frame) (value : Cell) (addr : Val) : Frame :=
  match boundedAddresses addr with
  | .known [a] => { f with mem := memSet a value f.mem }
  | .known xs => { f with mem := storeFold f (.plain value.val) (xs.filter (0 ≤ ·)) f.mem }
  | other =>
    let lo := other.bounds.1
    let hi := other.bounds.2
    let w := Cell.plain value.val
    { f with
      mem := f.mem.map fun e => if inInterval lo hi e.1 then (e.1, e.2.join w) else e
      rest := f.rest.join value.val }

def notVal (a : Val) : Val :=
  match a with
  | .known xs => .of (xs.foldr (fun x acc => insertS (if x = 0 then 1 else 0) acc) [])
  | other => if other.contains 0 then .known [0, 1] else .one 0

def notRel : Option Rel → Option Rel
  | some (.offset s off) => some (.test s off .eq 0)
  | some (.test s off c k) => some (.test s off c.negated k)
  | none => none

def branchS (rest : Option Frame) (cond : Cell) (zero : Bool) : Option (Option Frame) :=
  match withTop rest [] with
  | some f => (f.afterBranch cond zero).map some
  | none => some none

def canOther : Val → Bool
  | .known xs => xs.any (· ≠ 0)
  | _ => true

def condS (P : List Instr) (pc : Nat) (isJz : Bool) (rest : Option Frame) (cond off : Cell) : Step :=
  let canZero := cond.val.contains 0
  let taken := if isJz then canZero else canOther cond.val
  let falls := if isJz then canOther cond.val else canZero
  let t : Step := if taken then
      match branchS rest cond (isJz == true) with
      | some after => jumpS P pc off.val after
      | none => .empty
    else .empty
  let g : Step := if falls then
      match branchS rest cond (isJz == false) with
      | some after => land P ((pc : Int) + 1) after
      | none => .empty
    else .empty
  t.seq g

def binaryS (P : List Instr) (pc : Nat) (i : Instr) (rest : Option Frame) (a b : Cell) : Step :=
  let r := resultOf i a.val b.val
  let s1 : Step := if r.2 then .issue .overflow r.1.isNone else .empty
  let s2 : Step := match r.1 with
    | some v => land P ((pc : Int) + 1) (withTop rest [⟨v, relate i a b⟩])
    | none => .empty
  s1.seq s2

def divS (P : List Instr) (pc : Nat) (i : Instr) (rest : Option Frame) (a b : Cell) : Step :=
  let c := checkVal .divisionByZero b.val (· ≠ 0)
  if c.2 then
    let divisor : Val := match b.val with
      | .known xs => .of (xs.filter (· ≠ 0))
      | other => other
    let r := resultOf i a.val divisor
    let s1 : Step := if r.2 then .issue .overflow r.1.isNone else .empty
    let s2 : Step := match r.1 with
      | some v => land P ((pc : Int) + 1) (withTop rest [.plain v])
      | none => .empty
    c.1.seq (s1.seq s2)
  else c.1

/-- What `READ` can push, as the Rust builds it. Kept behind a name: nothing should evaluate it. -/
def readValues : List Int := (List.range 257).map fun k : Nat => (k : Int) - 1

def readVal : Val := .of readValues

/-- The operands are top first: `b` is the top, `a` the value below, as in the model. -/
def body (P : List Instr) (pc : Nat) (i : Instr) (rest : Option Frame) (ops : List Cell) : Step :=
  match i, ops with
  | .push n, _ => land P ((pc : Int) + 1) (withTop rest [.plain (.one (n.val : Int))])
  | .dup, [a] => copyS P pc rest a none
  | .over, [b, a] => copyS P pc rest a (some b)
  | .drop, [_] => land P ((pc : Int) + 1) (withTop rest [])
  | .swap, [b, a] => land P ((pc : Int) + 1) (withTop rest [a, b])
  | .rot, [c, b, a] => land P ((pc : Int) + 1) (withTop rest [a, c, b])
  | .add, [b, a] | .sub, [b, a] | .mul, [b, a] | .eq, [b, a] | .lt, [b, a] | .gt, [b, a] =>
    binaryS P pc i rest a b
  | .div, [b, a] | .mod, [b, a] => divS P pc i rest a b
  | .load, [a] =>
    let c := checkVal .negativeAddress a.val (0 ≤ ·)
    if c.2 then c.1.seq (land P ((pc : Int) + 1) (rest.map fun f => loadS f pc a.val)) else c.1
  | .store, [a, v] =>
    let c := checkVal .negativeAddress a.val (0 ≤ ·)
    if c.2 then c.1.seq (land P ((pc : Int) + 1) (rest.map fun f => storeS f v a.val)) else c.1
  | .jmp, [off] => jumpS P pc off.val (withTop rest [])
  | .jz, [off, c] => condS P pc true rest c off
  | .jnz, [off, c] => condS P pc false rest c off
  | .call, [off] => jumpS P pc off.val (withTop rest [.plain (.one ((pc : Int) + 1))])
  | .ret, [a] => retS P a.val (withTop rest [])
  | .halt, _ => ⟨[], [], false, true⟩
  | .read, _ =>
    land P ((pc : Int) + 1) (rest.map fun f =>
      let g := f.forget pc
      { g with stack := ⟨readVal, some (.offset pc 0)⟩ :: g.stack })
  | .write, [v] =>
    let c := checkVal .invalidByte v.val fun x => decide (0 ≤ x) && decide (x ≤ 255)
    if c.2 then c.1.seq (land P ((pc : Int) + 1) (withTop rest [])) else c.1
  | .not, [a] => land P ((pc : Int) + 1) (withTop rest [⟨notVal a.val, notRel a.rel⟩])
  | _, _ => .empty

def needed : Instr → Nat
  | .push _ | .halt | .read => 0
  | .dup | .drop | .load | .jmp | .write | .not | .call | .ret => 1
  | .rot => 3
  | _ => 2

def transfer (P : List Instr) (pc : Nat) (i : Instr) (frame : Option Frame) : Step :=
  match frame with
  | some f =>
    if f.stack.length < needed i then .issue .stackUnderflow true
    else body P pc i (some { f with stack := f.stack.drop (needed i) }) (f.stack.take (needed i))
  | none =>
    let s : Step := if needed i > 0 then .issue .stackUnderflow false else .empty
    s.seq (body P pc i none (List.replicate (needed i) (.plain .unknown)))

/-! ## What is recorded at a program point -/

structure Stacks where
  byDepth : List (Nat × Frame)
  unknown : Bool
  deriving DecidableEq

def Stacks.empty : Stacks := ⟨[], false⟩

def Stacks.variants (s : Stacks) : List (Option Frame) :=
  s.byDepth.map (fun e => some e.2) ++ if s.unknown then [none] else []

/-! ## The checker -/

/-- `g` describes all that `f` does. -/
def valCovers (g f : Val) : Bool :=
  match g, f with
  | .unknown, _ => true
  | .known ys, .known xs => xs.all ys.contains
  | .range lo hi, .known xs => xs.all fun x => decide (lo ≤ x) && decide (x ≤ hi)
  | .range lo hi, .range l h => decide (lo ≤ l) && decide (h ≤ hi)
  | _, _ => false

def cellCovers (g f : Cell) : Bool :=
  valCovers g.val f.val && (g.rel == none || g.rel == f.rel)

def stackCovers : List Cell → List Cell → Bool
  | [], [] => true
  | g :: gs, f :: fs => cellCovers g f && stackCovers gs fs
  | _, _ => false

/-- Every address either frame lists is covered, and unlisted addresses by `rest`. -/
def frameCovers (g f : Frame) : Bool :=
  stackCovers g.stack f.stack && valCovers g.rest f.rest &&
    f.mem.all (fun e => decide (0 ≤ e.1) && cellCovers (g.cellOf e.1) e.2) &&
    g.mem.all (fun e => decide (0 ≤ e.1) && cellCovers e.2 (f.cellOf e.1))

def stacksCover (s : Stacks) : Option Frame → Bool
  | none => s.unknown
  | some f =>
    s.unknown ||
      match s.byDepth.lookup f.stack.length with
      | some g => frameCovers g f
      | none => false

def recorded (R : List Stacks) (t : Nat) : Stacks := R.getD t .empty

/-- The check on a recorded result: it starts at the start, and is closed under `transfer`. -/
def checkResult (P : List Instr) (R : List Stacks) : Bool :=
  stacksCover (recorded R 0) (some .start) &&
    (List.range P.length).all fun pc =>
      (recorded R pc).variants.all fun v =>
        match P[pc]? with
        | none => true
        | some i =>
          let st := transfer P pc i v
          st.next.all (fun e => stacksCover (recorded R e.1) e.2) &&
            (!st.wild || (List.range P.length).all fun t => (recorded R t).unknown)

/-- The issues of a recorded result. An empty program has one, as in the Rust. -/
def issuesAt (P : List Instr) (R : List Stacks) (pc : Nat) : List (Kind × Bool) :=
  match P[pc]? with
  | none => []
  | some i => (recorded R pc).variants.flatMap fun v => (transfer P pc i v).issues

def haltsReported (P : List Instr) (R : List Stacks) : Bool :=
  (List.range P.length).any fun pc =>
    match P[pc]? with
    | none => false
    | some i => (recorded R pc).variants.any fun v => (transfer P pc i v).halts

/-! ## The concretization -/

def relHolds (σ : Nat → Int) : Option Rel → Int → Prop
  | none, _ => True
  | some (.offset s off), v => v = σ s + off
  | some (.test s off c k), v => v = if c.holds (σ s + off) k then 1 else 0

def cellOk (σ : Nat → Int) (c : Cell) (v : Int) : Prop := c.val.has v ∧ relHolds σ c.rel v

def AllOk (σ : Nat → Int) : List Cell → List Int → Prop
  | [], [] => True
  | c :: cs, v :: vs => cellOk σ c v ∧ AllOk σ cs vs
  | _, _ => False

/-- Memory: every listed cell holds at its address, and an unlisted one is in `rest`. -/
def MemOk (σ : Nat → Int) (l : List (Int × Cell)) (rest : Val) (m : Nat → Int) : Prop :=
  (∀ e ∈ l, 0 ≤ e.1 ∧ cellOk σ e.2 (m e.1.toNat)) ∧
    ∀ a : Nat, memGet l a = none → rest.has (m a)

def FrameOk (σ : Nat → Int) (f : Frame) (st : List Int) (m : Nat → Int) : Prop :=
  AllOk σ f.stack st ∧ MemOk σ f.mem f.rest m

/-- A frame describes a stack and a memory if some environment for its symbols fits. `none`
describes everything. -/
def Describes : Option Frame → List Int → (Nat → Int) → Prop
  | none, _, _ => True
  | some f, st, m => ∃ σ, FrameOk σ f st m

/-! ## Values -/

theorem listMin_le {xs : List Int} {v : Int} (h : v ∈ xs) : listMin xs ≤ v := by
  induction xs with
  | nil => simp at h
  | cons x l ih =>
    simp only [listMin, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := ih h'
      simp only [listMin] at this
      omega

theorem le_listMax {xs : List Int} {v : Int} (h : v ∈ xs) : v ≤ listMax xs := by
  induction xs with
  | nil => simp at h
  | cons x l ih =>
    simp only [listMax, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := ih h'
      simp only [listMax] at this
      omega

/-- Every 64-bit value of a `Val` is within its bounds. -/
theorem has_bounds {a : Val} {v : Int} (h : a.has v) (hv : InI64 v) :
    a.bounds.1 ≤ v ∧ v ≤ a.bounds.2 := by
  cases a with
  | known xs => exact ⟨listMin_le h, le_listMax h⟩
  | range lo hi => exact h
  | unknown => exact hv

theorem mkRange_has {lo hi v : Int} (h1 : lo ≤ v) (h2 : v ≤ hi) : (Val.mkRange lo hi).has v := by
  unfold Val.mkRange
  split
  · rename_i he
    simp only [Val.one, Val.has, List.mem_singleton]
    omega
  · split
    · trivial
    · exact ⟨h1, h2⟩

theorem of_has {xs : List Int} {v : Int} (h : v ∈ xs) : (Val.of xs).has v := by
  unfold Val.of
  split
  · exact mkRange_has (listMin_le h) (le_listMax h)
  · exact h

theorem mem_insertS {x y : Int} {l : List Int} : y ∈ insertS x l ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil => simp [insertS]
  | cons z l ih =>
    simp only [insertS]
    split
    · simp
    · split
      · rename_i he
        simp only [List.mem_cons]
        subst he
        constructor
        · intro h
          exact .inr h
        · rintro (rfl | h)
          · exact .inl rfl
          · exact h
      · simp only [List.mem_cons, ih]
        constructor
        · rintro (h | h | h)
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)
        · rintro (h | h | h)
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)

theorem mem_unionS {x y : List Int} {v : Int} : v ∈ unionS x y ↔ v ∈ x ∨ v ∈ y := by
  induction y with
  | nil => simp [unionS]
  | cons z l ih =>
    simp only [unionS, List.foldr_cons] at ih ⊢
    rw [mem_insertS, ih]
    simp only [List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

theorem join_left {a b : Val} {v : Int} (h : a.has v) (hv : InI64 v) : (a.join b).has v := by
  have hb := has_bounds h hv
  unfold Val.join
  split
  · split
    · exact h
    · exact of_has (mem_unionS.mpr (.inl h))
  · exact mkRange_has (by omega) (by omega)

theorem join_right {a b : Val} {v : Int} (h : b.has v) (hv : InI64 v) : (a.join b).has v := by
  have hb := has_bounds h hv
  unfold Val.join
  split
  · split
    · rename_i x y he
      subst he
      exact h
    · exact of_has (mem_unionS.mpr (.inr h))
  · exact mkRange_has (by omega) (by omega)

theorem contains_of_has {a : Val} {v : Int} (h : a.has v) : a.contains v = true := by
  cases a with
  | known xs => simpa [Val.contains, Val.has] using h
  | range lo hi =>
    obtain ⟨h1, h2⟩ := h
    simp [Val.contains, h1, h2]
  | unknown => rfl

theorem single_eq {a : Val} {k v : Int} (h : a.single = some k) (hv : a.has v) : v = k := by
  cases a with
  | known xs =>
    match xs, h with
    | [x], h =>
      simp only [Val.single, Option.some.injEq] at h
      subst h
      simpa [Val.has] using hv
  | range lo hi => simp [Val.single] at h
  | unknown => simp [Val.single] at h

theorem holds_iff (c : Cmp) (x b : Int) :
    c.holds x b = true ↔
      match c with
      | .eq => x = b
      | .ne => x ≠ b
      | .lt => x < b
      | .ge => x ≥ b
      | .gt => x > b
      | .le => x ≤ b := by
  cases c <;> simp [Cmp.holds]

theorem holds_shift (c : Cmp) (x b off : Int) : c.holds (x + off) (b + off) = c.holds x b := by
  cases c <;> simp only [Cmp.holds] <;> rw [Bool.eq_iff_iff] <;> simp <;> omega

theorem holds_negated (c : Cmp) (x b : Int) : c.negated.holds x b = !c.holds x b := by
  cases c <;> simp only [Cmp.negated, Cmp.holds] <;> rw [Bool.eq_iff_iff] <;> simp <;> omega

theorem finishB_has {l h v : Int} (h1 : l ≤ v) (h2 : v ≤ h) :
    ∃ a', finishB l h = some a' ∧ a'.has v := by
  refine ⟨Val.mkRange l h, ?_, mkRange_has h1 h2⟩
  unfold finishB
  rw [ite_eq_right (by omega)]

theorem restrictB_has {lo hi b v : Int} {c : Cmp} (h1 : lo ≤ v) (h2 : v ≤ hi) (hv : InI64 v)
    (hb : InI64 b) (hc : c.holds v b = true) : ∃ a', restrictB lo hi c b = some a' ∧ a'.has v := by
  have hmin : i64Min = -9223372036854775808 := rfl
  have hmax : i64Max = 9223372036854775807 := rfl
  have hI : i64Min ≤ v ∧ v ≤ i64Max := hv
  have hJ : i64Min ≤ b ∧ b ≤ i64Max := hb
  cases c with
  | eq =>
    simp [Cmp.holds] at hc
    exact finishB_has (by omega) (by omega)
  | ne =>
    simp [Cmp.holds] at hc
    refine finishB_has ?_ ?_
    · split <;> omega
    · split <;> omega
  | lt =>
    simp [Cmp.holds] at hc
    have hk : InI64 (b - 1) := by
      unfold InI64
      omega
    simp only [restrictB, checkedI]
    rw [ite_eq_left hk]
    exact finishB_has h1 (by omega)
  | ge =>
    simp [Cmp.holds] at hc
    exact finishB_has (by omega) h2
  | gt =>
    simp [Cmp.holds] at hc
    have hk : InI64 (b + 1) := by
      unfold InI64
      omega
    simp only [restrictB, checkedI]
    rw [ite_eq_left hk]
    exact finishB_has (by omega) h2
  | le =>
    simp [Cmp.holds] at hc
    exact finishB_has h1 (by omega)

/-- Restricting keeps every 64-bit value that satisfies the comparison. -/
theorem restrict_has {a : Val} {c : Cmp} {b v : Int} (h : a.has v) (hv : InI64 v) (hb : InI64 b)
    (hc : c.holds v b = true) : ∃ a', a.restrict c b = some a' ∧ a'.has v := by
  have hbd := has_bounds h hv
  cases a with
  | known xs =>
    have hm : v ∈ xs.filter (fun x => c.holds x b) := List.mem_filter.mpr ⟨h, hc⟩
    simp only [Val.restrict]
    split
    · rename_i he
      rw [he] at hm
      simp at hm
    · exact ⟨_, rfl, of_has hm⟩
  | range lo hi => exact restrictB_has hbd.1 hbd.2 hv hb hc
  | unknown => exact restrictB_has hbd.1 hbd.2 hv hb hc

/-! ## Relations -/

def upd (σ : Nat → Int) (s : Nat) (x : Int) : Nat → Int := fun k => if k = s then x else σ k

theorem forgetCell_ok {σ : Nat → Int} {c : Cell} {v x : Int} (sym : Nat) (h : cellOk σ c v) :
    cellOk (upd σ sym x) (forgetCell sym c) v := by
  obtain ⟨h1, h2⟩ := h
  unfold forgetCell
  cases hr : c.rel with
  | none =>
    refine ⟨h1, ?_⟩
    rw [hr]
    trivial
  | some r =>
    simp only
    split
    · exact ⟨h1, trivial⟩
    · rename_i hne
      refine ⟨h1, ?_⟩
      rw [hr] at h2 ⊢
      cases r with
      | offset s off =>
        simp only [Rel.sym] at hne
        simp only [relHolds, upd] at h2 ⊢
        rw [ite_eq_right hne]
        exact h2
      | test s off cc k =>
        simp only [Rel.sym] at hne
        simp only [relHolds] at h2
        simp only [relHolds, upd, hne, ↓reduceIte]
        exact h2

theorem allOk_forget {σ : Nat → Int} {x : Int} (sym : Nat) {cs : List Cell} {vs : List Int}
    (h : AllOk σ cs vs) : AllOk (upd σ sym x) (cs.map (forgetCell sym)) vs := by
  induction cs generalizing vs with
  | nil =>
    cases vs with
    | nil => trivial
    | cons _ _ => exact h
  | cons c cs ih =>
    cases vs with
    | nil => exact h
    | cons v vs => exact ⟨forgetCell_ok sym h.1, ih h.2⟩

theorem memGet_none_of_map {l : List (Int × Cell)} {f : Cell → Cell} {a : Int}
    (h : memGet (l.map fun e => (e.1, f e.2)) a = none) : memGet l a = none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [memGet, List.map_cons, List.find?_cons] at h ⊢
    by_cases he : (e.1 == a) = true
    · simp [he] at h
    · simp only [he] at h ⊢
      exact ih h

theorem forget_ok {σ : Nat → Int} {f : Frame} {st : List Int} {m : Nat → Int} {x : Int} (sym : Nat)
    (h : FrameOk σ f st m) : FrameOk (upd σ sym x) (f.forget sym) st m := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨allOk_forget sym h1, ?_, ?_⟩
  · intro e he
    simp only [Frame.forget, List.mem_map] at he
    obtain ⟨e', hm, rfl⟩ := he
    exact ⟨(h2 e' hm).1, forgetCell_ok sym (h2 e' hm).2⟩
  · intro a ha
    exact h3 a (memGet_none_of_map ha)

theorem memGet_mem {l : List (Int × Cell)} {a : Int} {c : Cell} (h : memGet l a = some c) :
    (a, c) ∈ l := by
  induction l with
  | nil => simp [memGet] at h
  | cons e l ih =>
    simp only [memGet, List.find?_cons] at h
    by_cases he : (e.1 == a) = true
    · simp only [he, Option.map_some, Option.some.injEq] at h
      have : e.1 = a := by simpa using he
      subst this
      subst h
      exact .head _
    · simp only [he] at h
      exact .tail _ (ih h)

theorem mem_insertAt {k : Int} {c : Cell} {l : List (Int × Cell)} {e : Int × Cell} :
    e ∈ insertAt k c l ↔ e = (k, c) ∨ e ∈ l := by
  induction l with
  | nil => simp [insertAt]
  | cons x l ih =>
    simp only [insertAt]
    split
    · simp
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)

theorem mem_memSet {k : Int} {c : Cell} {l : List (Int × Cell)} {e : Int × Cell} :
    e ∈ memSet k c l ↔ e = (k, c) ∨ (e ∈ l ∧ e.1 ≠ k) := by
  simp [memSet, mem_insertAt, List.mem_filter]

theorem memGet_none_iff {l : List (Int × Cell)} {a : Int} :
    memGet l a = none ↔ ∀ e ∈ l, e.1 ≠ a := by
  simp [memGet, List.find?_eq_none]

theorem memGet_memSet_none {k : Int} {c : Cell} {l : List (Int × Cell)} {a : Int}
    (h : memGet (memSet k c l) a = none) : a ≠ k ∧ memGet l a = none := by
  rw [memGet_none_iff] at h ⊢
  have hne : a ≠ k := fun he => h (k, c) (mem_memSet.mpr (.inl rfl)) he.symm
  refine ⟨hne, fun e he hea => ?_⟩
  exact h e (mem_memSet.mpr (.inr ⟨he, by rw [hea]; exact hne⟩)) hea

/-- The cell at an address holds what memory holds, listed or not. -/
theorem cellOf_ok {σ : Nat → Int} {f : Frame} {st : List Int} {m : Nat → Int} {a : Nat}
    (h : FrameOk σ f st m) : cellOk σ (f.cellOf a) (m a) := by
  obtain ⟨_, h2, h3⟩ := h
  unfold Frame.cellOf
  cases hg : memGet f.mem a with
  | none => exact ⟨h3 a hg, trivial⟩
  | some c =>
    have := (h2 _ (memGet_mem hg)).2
    simpa using this

theorem cellVal_has {σ : Nat → Int} {f : Frame} {st : List Int} {m : Nat → Int} {a : Nat}
    (h : FrameOk σ f st m) : (f.cellVal a).has (m a) := by
  obtain ⟨_, h2, h3⟩ := h
  unfold Frame.cellVal
  cases hg : memGet f.mem a with
  | none => exact h3 a hg
  | some c =>
    have := (h2 _ (memGet_mem hg)).2.1
    simpa using this

/-! ## Narrowing -/

theorem narrowCell_ok {σ : Nat → Int} {cell : Cell} {v : Int} {sym : Nat} {c : Cmp} {b : Int}
    (h : cellOk σ cell v) (hv : InI64 v) (hc : c.holds (σ sym) b = true) :
    ∃ cell', narrowCell sym c b cell = some cell' ∧ cellOk σ cell' v := by
  unfold narrowCell
  split
  · rename_i s off hr
    split
    · rename_i hcond
      obtain ⟨hs, hb⟩ := hcond
      subst hs
      have hrel : v = σ s + off := by
        have := h.2
        rw [hr] at this
        exact this
      have hh : c.holds v (b + off) = true := by
        rw [hrel, holds_shift]
        exact hc
      obtain ⟨a', ha, hk⟩ := restrict_has h.1 hv hb hh
      refine ⟨{ cell with val := a' }, by simp [ha], hk, h.2⟩
    · exact ⟨cell, rfl, h⟩
  · exact ⟨cell, rfl, h⟩

theorem narrowStack_ok {σ : Nat → Int} {cs : List Cell} {vs : List Int} {sym : Nat} {c : Cmp}
    {b : Int} (h : AllOk σ cs vs) (hv : ∀ v ∈ vs, InI64 v) (hc : c.holds (σ sym) b = true) :
    ∃ cs', narrowStack sym c b cs = some cs' ∧ AllOk σ cs' vs := by
  induction cs generalizing vs with
  | nil =>
    exact ⟨[], rfl, h⟩
  | cons x l ih =>
    cases vs with
    | nil => exact h.elim
    | cons v vs =>
      obtain ⟨x', hx, hxok⟩ := narrowCell_ok h.1 (hv v (.head _)) hc
      obtain ⟨l', hl, hlok⟩ := ih h.2 (fun w hw => hv w (.tail _ hw))
      exact ⟨x' :: l', by simp [narrowStack, hx, hl], hxok, hlok⟩

theorem narrowMem_ok {σ : Nat → Int} {l : List (Int × Cell)} {m : Nat → Int} {sym : Nat} {c : Cmp}
    {b : Int} (h : ∀ e ∈ l, 0 ≤ e.1 ∧ cellOk σ e.2 (m e.1.toNat)) (hv : ∀ j, InI64 (m j))
    (hc : c.holds (σ sym) b = true) :
    ∃ l', narrowMem sym c b l = some l' ∧ (∀ e ∈ l', 0 ≤ e.1 ∧ cellOk σ e.2 (m e.1.toNat)) ∧
      ∀ a, memGet l' a = none → memGet l a = none := by
  induction l with
  | nil => exact ⟨[], rfl, by simp, fun _ _ => rfl⟩
  | cons e l ih =>
    obtain ⟨h0, hok⟩ := h e (.head _)
    obtain ⟨x', hx, hxok⟩ := narrowCell_ok hok (hv _) hc
    obtain ⟨l', hl, hlok, hnone⟩ := ih (fun e' he' => h e' (.tail _ he'))
    refine ⟨(e.1, x') :: l', by simp [narrowMem, hx, hl], ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | hin
      · exact ⟨h0, hxok⟩
      · exact hlok e' hin
    · intro a ha
      rw [memGet_none_iff] at ha ⊢
      intro y hy
      rcases List.mem_cons.mp hy with he | hin
      · rw [he]
        exact ha (e.1, x') (.head _)
      · have := hnone a (memGet_none_iff.mpr fun w hw => ha w (.tail _ hw))
        exact memGet_none_iff.mp this y hin

theorem narrow_ok {σ : Nat → Int} {f : Frame} {st : List Int} {m : Nat → Int} {sym : Nat} {c : Cmp}
    {b : Int} (h : FrameOk σ f st m) (hst : ∀ v ∈ st, InI64 v) (hv : ∀ j, InI64 (m j))
    (hc : c.holds (σ sym) b = true) :
    ∃ f', f.narrow sym c b = some f' ∧ FrameOk σ f' st m := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨s', hs, hsok⟩ := narrowStack_ok h1 hst hc
  obtain ⟨l', hl, hlok, hnone⟩ := narrowMem_ok h2 hv hc
  refine ⟨{ f with stack := s', mem := l' }, by simp [Frame.narrow, hs, hl], hsok, hlok, ?_⟩
  intro a ha
  exact h3 a (hnone a ha)

/-- A branch on a value with a relation narrows only what the branch implies. -/
theorem afterBranch_ok {σ : Nat → Int} {f : Frame} {st : List Int} {m : Nat → Int} {cond : Cell}
    {x : Int} {zero : Bool} (h : FrameOk σ f st m) (hst : ∀ v ∈ st, InI64 v)
    (hv : ∀ j, InI64 (m j)) (hx : cellOk σ cond x) (hz : (x = 0) ↔ zero = true) :
    ∃ f', f.afterBranch cond zero = some f' ∧ FrameOk σ f' st m := by
  unfold Frame.afterBranch
  have hrel := hx.2
  cases hr : cond.rel with
  | none => exact ⟨f, rfl, h⟩
  | some r =>
    rw [hr] at hrel
    cases r with
    | offset sym off =>
      simp only [relHolds] at hrel
      simp only
      split
      · apply narrow_ok h hst hv
        cases zero with
        | true =>
          have : x = 0 := hz.mpr rfl
          simp [Cmp.holds]
          omega
        | false =>
          have : x ≠ 0 := fun e => by simpa using hz.mp e
          simp [Cmp.holds]
          omega
      · exact ⟨f, rfl, h⟩
    | test sym off c k =>
      simp only [relHolds] at hrel
      simp only
      split
      · apply narrow_ok h hst hv
        have hs : c.holds (σ sym) (k - off) = c.holds (σ sym + off) k := by
          have := holds_shift c (σ sym) (k - off) off
          rw [show k - off + off = k by omega] at this
          exact this.symm
        cases zero with
        | true =>
          have h0 : x = 0 := hz.mpr rfl
          simp only [↓reduceIte, holds_negated, hs]
          cases hh : c.holds (σ sym + off) k with
          | true =>
            rw [hh] at hrel
            simp at hrel
            omega
          | false => rfl
        | false =>
          have h0 : x ≠ 0 := fun e => by simpa using hz.mp e
          simp only [Bool.false_eq_true, ↓reduceIte, hs]
          cases hh : c.holds (σ sym + off) k with
          | true => rfl
          | false =>
            rw [hh] at hrel
            simp at hrel
            omega
      · exact ⟨f, rfl, h⟩

/-! ## Results of arithmetic -/

theorem insertS_mono {x v : Int} {l : List Int} (h : v ∈ l) : v ∈ insertS x l :=
  mem_insertS.mpr (.inr h)

theorem pairs_inner_mono (f : Int → Int → Option Int) (x : Int) (ys : List Int)
    (acc : List Int × Bool) {v : Int} (h : v ∈ acc.1) :
    v ∈ (ys.foldl (fun acc y =>
      match f x y with
      | some w => (insertS w acc.1, acc.2)
      | none => (acc.1, true)) acc).1 := by
  induction ys generalizing acc with
  | nil => exact h
  | cons y l ih =>
    simp only [List.foldl_cons]
    apply ih
    cases f x y with
    | none => exact h
    | some w => exact insertS_mono h

theorem pairs_inner_new (f : Int → Int → Option Int) (x : Int) (ys : List Int)
    (acc : List Int × Bool) {y r : Int} (hy : y ∈ ys) (hf : f x y = some r) :
    r ∈ (ys.foldl (fun acc y =>
      match f x y with
      | some w => (insertS w acc.1, acc.2)
      | none => (acc.1, true)) acc).1 := by
  induction ys generalizing acc with
  | nil => simp at hy
  | cons z l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hin
    · apply pairs_inner_mono
      simp [hf, mem_insertS]
    · exact ih _ hin

theorem pairs_outer_mono (f : Int → Int → Option Int) (xs ys : List Int) (acc : List Int × Bool)
    {v : Int} (h : v ∈ acc.1) :
    v ∈ (xs.foldl (fun acc x =>
      ys.foldl (fun acc y =>
        match f x y with
        | some w => (insertS w acc.1, acc.2)
        | none => (acc.1, true)) acc) acc).1 := by
  induction xs generalizing acc with
  | nil => exact h
  | cons x l ih =>
    simp only [List.foldl_cons]
    exact ih _ (pairs_inner_mono f x ys acc h)

theorem pairsOut_mem {f : Int → Int → Option Int} {xs ys : List Int} {x y r : Int} (hx : x ∈ xs)
    (hy : y ∈ ys) (hf : f x y = some r) : r ∈ (pairsOut f xs ys).1 := by
  unfold pairsOut
  generalize ((([] : List Int), false) : List Int × Bool) = acc
  induction xs generalizing acc with
  | nil => simp at hx
  | cons z l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hin
    · exact pairs_outer_mono f l ys _ (pairs_inner_new f _ ys acc hy hf)
    · exact ih hin _

/-- A `some` result of `binFn` in 64 bits is in the result set, enumerated or on bounds. -/
theorem boundAdd_low {x y al bl : Int} (hx : al ≤ x) (hy : bl ≤ y) (hr : InI64 (x + y)) :
    boundAdd al bl i64Min ≤ x + y := by
  have hI : i64Min ≤ x + y ∧ x + y ≤ i64Max := hr
  unfold boundAdd
  split
  · exact hI.1
  · unfold checkedI
    by_cases hc : InI64 (al + bl)
    · rw [ite_eq_left hc]
      show al + bl ≤ x + y
      omega
    · rw [ite_eq_right hc]
      exact hI.1

theorem boundAdd_high {x y ah bh : Int} (hx : x ≤ ah) (hy : y ≤ bh) (hr : InI64 (x + y)) :
    x + y ≤ boundAdd ah bh i64Max := by
  have hI : i64Min ≤ x + y ∧ x + y ≤ i64Max := hr
  unfold boundAdd
  split
  · exact hI.2
  · unfold checkedI
    by_cases hc : InI64 (ah + bh)
    · rw [ite_eq_left hc]
      show x + y ≤ ah + bh
      omega
    · rw [ite_eq_right hc]
      exact hI.2

theorem b2i_verdict_true {p : Prop} [Decidable p] (h : p) : b2i p = 1 := by
  simp [b2i, h]

theorem b2i_verdict_false {p : Prop} [Decidable p] (h : ¬ p) : b2i p = 0 := by
  simp [b2i, h]

theorem b2i_either (p : Prop) [Decidable p] : (Val.known [0, 1]).has (b2i p) := by
  unfold b2i
  split <;> simp [Val.has]

theorem onBounds_has_nz {i : Instr} {a b : Val} {x y r : Int} (hx : a.has x) (hy : b.has y)
    (hxI : InI64 x) (hyI : InI64 y) (hr : binFn i x y = some r) (hrI : InI64 r)
    (hi : i = .mod → y ≠ 0) : (onBounds i a b).has r := by
  have hA := has_bounds hx hxI
  have hB := has_bounds hy hyI
  unfold onBounds
  cases i with
  | add =>
    simp only [binFn, checkedI] at hr
    split at hr
    · cases hr
      exact mkRange_has (boundAdd_low hA.1 hB.1 hrI) (boundAdd_high hA.2 hB.2 hrI)
    · cases hr
  | sub =>
    simp only [binFn, checkedI] at hr
    split at hr
    · cases hr
      simp only
      split
      · have e : x - y = x + -y := by omega
        rw [e] at hrI ⊢
        exact mkRange_has (boundAdd_low hA.1 (by omega) hrI) (boundAdd_high hA.2 (by omega) hrI)
      · trivial
    · cases hr
  | eq =>
    simp only [binFn, Option.some.injEq] at hr
    subst hr
    simp only
    split
    · have hne : x ≠ y := by omega
      rw [b2i_verdict_false hne]
      simp [Val.one, Val.has]
    · exact b2i_either _
  | lt =>
    simp only [binFn, Option.some.injEq] at hr
    subst hr
    simp only
    split
    · rw [b2i_verdict_true (by omega)]
      simp [Val.one, Val.has]
    · split
      · rw [b2i_verdict_false (by omega)]
        simp [Val.one, Val.has]
      · exact b2i_either _
  | gt =>
    simp only [binFn, Option.some.injEq] at hr
    subst hr
    simp only
    split
    · rw [b2i_verdict_true (by omega)]
      simp [Val.one, Val.has]
    · split
      · rw [b2i_verdict_false (by omega)]
        simp [Val.one, Val.has]
      · exact b2i_either _
  | mod =>
    simp only [binFn, Option.some.injEq] at hr
    subst hr
    have hy0 := hi rfl
    simp only
    split
    · have hna : (Int.tmod x y).natAbs = x.natAbs % y.natAbs := Int.natAbs_tmod x y
      have hlt : x.natAbs % y.natAbs < y.natAbs := Nat.mod_lt _ (by omega)
      have hyy : i64Min ≤ y ∧ y ≤ i64Max := hyI
      have hmin : i64Min = -9223372036854775808 := rfl
      have hmax : i64Max = 9223372036854775807 := rfl
      split
      · rename_i hal
        have hx0 : 0 ≤ x := by omega
        have hr0 := Int.tmod_nonneg y hx0
        exact mkRange_has hr0 (by omega)
      · exact mkRange_has (by omega) (by omega)
    · trivial
  | mul | div | push _ | dup | drop | swap | over | rot | load | store | jmp | jz | jnz | halt
  | call | ret | read | write | not => trivial

/-- The value of an operation is in what `resultOf` says, when it fits in 64 bits. -/
theorem resultOf_has {i : Instr} {a b : Val} {x y r : Int} (hx : a.has x) (hy : b.has y)
    (hxI : InI64 x) (hyI : InI64 y) (hr : binFn i x y = some r) (hrI : InI64 r)
    (hi : i = .mod → y ≠ 0) : ∃ v, (resultOf i a b).1 = some v ∧ v.has r := by
  unfold resultOf
  cases hl : lift2 a b (binFn i) with
  | none => exact ⟨_, rfl, onBounds_has_nz hx hy hxI hyI hr hrI hi⟩
  | some res =>
    unfold lift2 at hl
    split at hl
    · rename_i xs ys
      split at hl
      · cases hl
      · cases hl
        have hm := pairsOut_mem (f := binFn i) hx hy hr
        simp only
        split
        · rename_i he
          rw [he] at hm
          simp at hm
        · exact ⟨_, rfl, of_has hm⟩
    · cases hl

theorem offsetPlus_ok {σ : Nat → Int} {c : Cell} {x k : Int} (h : cellOk σ c x) :
    relHolds σ (offsetPlus c k) (x + k) := by
  unfold offsetPlus
  have hrel := h.2
  split
  · rename_i s off hr
    rw [hr] at hrel
    simp only [relHolds] at hrel
    unfold checkedI
    split
    · simp only [Option.map_some, relHolds]
      omega
    · trivial
  · trivial

theorem offsetMinus_ok {σ : Nat → Int} {c : Cell} {x k : Int} (h : cellOk σ c x) :
    relHolds σ (offsetMinus c k) (x - k) := by
  unfold offsetMinus
  have hrel := h.2
  split
  · rename_i s off hr
    rw [hr] at hrel
    simp only [relHolds] at hrel
    unfold checkedI
    split
    · simp only [Option.map_some, relHolds]
      omega
    · trivial
  · trivial

theorem testOf_ok {σ : Nat → Int} {c : Cell} {x r k : Int} {cmp : Cmp} (h : cellOk σ c x)
    (hr : r = if cmp.holds x k then 1 else 0) : relHolds σ (testOf c cmp k) r := by
  unfold testOf
  have hrel := h.2
  split
  · rename_i s off he
    rw [he] at hrel
    simp only [relHolds] at hrel
    simp only [relHolds]
    rw [hr, hrel]
  · trivial

/-- `relate` is sound: the relation it keeps holds of the result. -/
theorem relate_ok {σ : Nat → Int} {i : Instr} {a b : Cell} {x y r : Int} (hx : cellOk σ a x)
    (hy : cellOk σ b y) (hr : binFn i x y = some r) : relHolds σ (relate i a b) r := by
  have hsingleB : ∀ {k}, b.val.single = some k → y = k := fun hk => single_eq hk hy.1
  have hsingleA : ∀ {k}, a.val.single = some k → x = k := fun hk => single_eq hk hx.1
  cases i with
  | add =>
    simp only [binFn, checkedI] at hr
    split at hr
    · cases hr
      simp only [relate]
      split
      · rename_i k _ hb
        have := hsingleB hb
        subst this
        exact offsetPlus_ok hx
      · rename_i k _ ha
        have := hsingleA ha
        subst this
        rw [Int.add_comm]
        exact offsetPlus_ok hy
      · trivial
    · cases hr
  | sub =>
    simp only [binFn, checkedI] at hr
    split at hr
    · cases hr
      simp only [relate]
      split
      · rename_i k hb
        have := hsingleB hb
        subst this
        exact offsetMinus_ok hx
      · trivial
    · cases hr
  | eq =>
    simp only [binFn, Option.some.injEq] at hr
    subst hr
    simp only [relate]
    split
    · rename_i k _ hb
      have := hsingleB hb
      subst this
      exact testOf_ok hx (by simp [b2i, Cmp.holds])
    · rename_i k _ ha
      have := hsingleA ha
      subst this
      refine testOf_ok hy ?_
      by_cases he : x = y
      · simp [b2i, Cmp.holds, he]
      · have : ¬ y = x := fun e => he e.symm
        simp [b2i, Cmp.holds, he, this]
    · trivial
  | lt =>
    simp only [binFn, Option.some.injEq] at hr
    subst hr
    simp only [relate]
    split
    · rename_i k _ hb
      have := hsingleB hb
      subst this
      exact testOf_ok hx (by simp [b2i, Cmp.holds])
    · rename_i k _ ha
      have := hsingleA ha
      subst this
      exact testOf_ok hy (by simp [b2i, Cmp.holds])
    · trivial
  | gt =>
    simp only [binFn, Option.some.injEq] at hr
    subst hr
    simp only [relate]
    split
    · rename_i k _ hb
      have := hsingleB hb
      subst this
      exact testOf_ok hx (by simp [b2i, Cmp.holds])
    · rename_i k _ ha
      have := hsingleA ha
      subst this
      exact testOf_ok hy (by simp [b2i, Cmp.holds])
    · trivial
  | mul | div | mod | push _ | dup | drop | swap | over | rot | load | store | jmp | jz | jnz | halt
  | call | ret | read | write | not => trivial

/-! ## Successors and issues -/

/-- `s'` is covered by a successor of this step, or the step gave up and said so. -/
def Succ (T : Step) (t : Nat) (st : List Int) (m : Nat → Int) : Prop :=
  T.wild = true ∨ ∃ g, (t, g) ∈ T.next ∧ Describes g st m

theorem Succ.seq_left {A : Step} {t : Nat} {st : List Int} {m : Nat → Int} (B : Step)
    (h : Succ A t st m) : Succ (A.seq B) t st m := by
  rcases h with h | ⟨g, hg, hd⟩
  · exact .inl (by simp [Step.seq, h])
  · exact .inr ⟨g, by simp [Step.seq, hg], hd⟩

theorem Succ.seq_right {B : Step} {t : Nat} {st : List Int} {m : Nat → Int} (A : Step)
    (h : Succ B t st m) : Succ (A.seq B) t st m := by
  rcases h with h | ⟨g, hg, hd⟩
  · exact .inl (by simp [Step.seq, h])
  · exact .inr ⟨g, by simp [Step.seq, hg], hd⟩

theorem jumpTo_some {P : List Instr} {t s' : State} {x : Int} (h : jumpTo P t x = .next s') :
    0 ≤ x ∧ x < (P.length : Int) ∧ s' = { t with pc := x.toNat } := by
  unfold jumpTo at h
  split at h
  · rename_i hc
    exact ⟨hc.1, hc.2, (Outcome.next.inj h).symm⟩
  · cases h

/-- Landing where the model lands. -/
theorem land_succ {P : List Instr} {t s' : State} {x : Int} {after : Option Frame}
    (h : jumpTo P t x = .next s') (hd : Describes after t.stack t.mem) :
    Succ (land P x after) s'.pc s'.stack s'.mem := by
  obtain ⟨h1, h2, rfl⟩ := jumpTo_some h
  refine .inr ⟨after, ?_, hd⟩
  unfold land
  rw [ite_eq_left ⟨h1, h2⟩]
  exact .head _

theorem fold_land_next {P : List Instr} {g : Int → Int} {after : Option Frame} (xs : List Int)
    (acc : Step) {e : Nat × Option Frame} (h : e ∈ acc.next) :
    e ∈ (xs.foldl (fun acc o => acc.seq (land P (g o) after)) acc).next := by
  induction xs generalizing acc with
  | nil => exact h
  | cons x l ih =>
    simp only [List.foldl_cons]
    exact ih _ (by simp [Step.seq, h])

theorem fold_land_succ {P : List Instr} {g : Int → Int} {after : Option Frame} {xs : List Int}
    {o : Int} (hmem : o ∈ xs) (acc : Step) {t : State} {s' : State}
    (h : jumpTo P t (g o) = .next s') (hd : Describes after t.stack t.mem) :
    ∃ gg, (s'.pc, gg) ∈ (xs.foldl (fun acc o => acc.seq (land P (g o) after)) acc).next ∧
      Describes gg s'.stack s'.mem := by
  induction xs generalizing acc with
  | nil => simp at hmem
  | cons x l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hin
    · rcases land_succ h hd with hw | ⟨gg, hg, hdd⟩
      · unfold land at hw
        split at hw <;> simp [Step.issue] at hw
      · exact ⟨gg, fold_land_next l _ (by simp [Step.seq, hg]), hdd⟩
    · exact ih hin _

theorem jumpS_succ {P : List Instr} {pc : Nat} {off : Val} {after : Option Frame} {o : Int}
    (ho : off.has o) {t s' : State} (h : jumpTo P t ((pc : Int) + o) = .next s')
    (hd : Describes after t.stack t.mem) : Succ (jumpS P pc off after) s'.pc s'.stack s'.mem := by
  unfold jumpS
  split
  · exact .inr (fold_land_succ (g := fun o => (pc : Int) + o) ho _ h hd)
  · exact .inl rfl

theorem retS_succ {P : List Instr} {addr : Val} {after : Option Frame} {a : Int}
    (ha : addr.has a) {t s' : State} (h : jumpTo P t a = .next s')
    (hd : Describes after t.stack t.mem) : Succ (retS P addr after) s'.pc s'.stack s'.mem := by
  unfold retS
  split
  · exact .inr (fold_land_succ (g := fun o => o) ha _ h hd)
  · exact .inl rfl

/-! ## Frames after one instruction -/

/-- What is left of a frame under its operands describes the rest of the stack. -/
def Desc (σ : Nat → Int) : Option Frame → List Int → (Nat → Int) → Prop
  | none, _, _ => True
  | some f, st, m => FrameOk σ f st m

theorem allOk_append {σ : Nat → Int} {cs ds : List Cell} {vs ws : List Int} (h1 : AllOk σ cs vs)
    (h2 : AllOk σ ds ws) : AllOk σ (cs ++ ds) (vs ++ ws) := by
  induction cs generalizing vs with
  | nil =>
    cases vs with
    | nil => exact h2
    | cons _ _ => exact h1.elim
  | cons c cs ih =>
    cases vs with
    | nil => exact h1.elim
    | cons v vs => exact ⟨h1.1, ih h1.2⟩

theorem withTop_ok {σ : Nat → Int} {rest : Option Frame} {r : List Int} {m : Nat → Int}
    {top : List Cell} {vals : List Int} (hr : Desc σ rest r m) (ht : AllOk σ top vals) :
    Describes (withTop rest top) (vals ++ r) m := by
  cases rest with
  | none => trivial
  | some f => exact ⟨σ, allOk_append ht hr.1, hr.2⟩

theorem cell_plain_ok {σ : Nat → Int} {a : Val} {v : Int} (h : a.has v) :
    cellOk σ (.plain a) v := ⟨h, trivial⟩

theorem one_ok {σ : Nat → Int} (v : Int) : cellOk σ (.plain (.one v)) v :=
  cell_plain_ok (by simp [Val.one, Val.has])

theorem desc_mono {σ : Nat → Int} {rest : Option Frame} {r : List Int} {m : Nat → Int}
    (h : Desc σ rest r m) (sym : Nat) (x : Int) :
    Desc (upd σ sym x) (rest.map (·.forget sym)) r m := by
  cases rest with
  | none => trivial
  | some f => exact forget_ok sym h

/-- A copy that gets a fresh symbol: the symbol is the value, and the old symbol is forgotten. -/
theorem copy_fresh_ok {σ : Nat → Int} {a : Cell} {x : Int} {pc : Nat} (h : cellOk σ a x) :
    cellOk (upd σ pc x) ⟨a.val, some (.offset pc 0)⟩ x :=
  ⟨h.1, by simp [relHolds, upd]⟩

/-! ## `check` -/

theorem filter_length_lt {xs : List Int} {p : Int → Bool} {v : Int} (hv : v ∈ xs)
    (hp : p v = false) : (xs.filter p).length < xs.length := by
  induction xs with
  | nil => simp at hv
  | cons x l ih =>
    rcases List.mem_cons.mp hv with rfl | hin
    · simp only [List.filter_cons, hp]
      have := List.length_filter_le p l
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have := ih hin
      simp only [List.filter_cons, List.length_cons]
      split <;> (try simp only [List.length_cons]) <;> omega

theorem checkVal_go {k : Kind} {value : Val} {allowed : Int → Bool} {v : Int} (hv : value.has v)
    (ha : allowed v = true) : (checkVal k value allowed).2 = true := by
  unfold checkVal
  split
  · rename_i xs
    have hm : v ∈ xs.filter allowed := List.mem_filter.mpr ⟨hv, ha⟩
    have : 0 < (xs.filter allowed).length := List.length_pos_of_mem hm
    simp only [decide_eq_true_eq]
    exact this
  · rfl

/-- A value that is not allowed is reported. -/
theorem checkVal_issue {k : Kind} {value : Val} {allowed : Int → Bool} {v : Int} (hv : value.has v)
    (hI : InI64 v) (ha : allowed v = false)
    (hb : ∀ lo hi : Int, lo ≤ v → v ≤ hi →
      (if k = .divisionByZero then decide (lo > 0) || decide (hi < 0)
        else allowed lo && allowed hi) = false) :
    ∃ c, (k, c) ∈ (checkVal k value allowed).1.issues := by
  unfold checkVal
  split
  · rename_i xs
    have := filter_length_lt (p := allowed) hv ha
    simp only
    rw [ite_eq_left this]
    exact ⟨_, .head _⟩
  · have hbd := has_bounds hv hI
    simp only
    rw [hb _ _ hbd.1 hbd.2]
    exact ⟨false, .head _⟩

/-! ## Memory -/

theorem boundedAddresses_has {a : Val} {x : Int} (h : a.has x) : (boundedAddresses a).has x := by
  unfold boundedAddresses
  split
  · rename_i xs
    split
    · exact mkRange_has (listMin_le h) (le_listMax h)
    · exact h
  · exact h

theorem cellVal_entry {f : Frame} {a : Int} {c : Cell} (h : memGet f.mem a = some c) :
    f.cellVal a = c.val := by
  simp [Frame.cellVal, h]

theorem loadFold_aux {f : Frame} {v : Int} (hv : InI64 v) (l : List Int) (acc : Option Val)
    (h : (∃ a ∈ l, (f.cellVal a).has v) ∨ ∃ w, acc = some w ∧ w.has v) :
    ((l.foldl (fun acc a =>
      match acc with
      | none => some (f.cellVal a)
      | some x => some (x.join (f.cellVal a))) acc).getD .unknown).has v := by
  induction l generalizing acc with
  | nil =>
    rcases h with ⟨a, ha, _⟩ | ⟨w, rfl, hw⟩
    · simp at ha
    · exact hw
  | cons y l ih =>
    simp only [List.foldl_cons]
    apply ih
    rcases h with ⟨a, ha, hav⟩ | ⟨w, rfl, hw⟩
    · rcases List.mem_cons.mp ha with rfl | hin
      · refine .inr ?_
        cases acc with
        | none => exact ⟨_, rfl, hav⟩
        | some x => exact ⟨_, rfl, join_right hav hv⟩
      · exact .inl ⟨a, hin, hav⟩
    · exact .inr ⟨_, rfl, join_left hw hv⟩

theorem foldJoin_has {v : Int} (hv : InI64 v) (l : List (Int × Cell)) (start : Val)
    (h : start.has v ∨ ∃ e ∈ l, e.2.val.has v) :
    (l.foldl (fun x e => x.join e.2.val) start).has v := by
  induction l generalizing start with
  | nil =>
    rcases h with h | ⟨e, he, _⟩
    · exact h
    · simp at he
  | cons y l ih =>
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | ⟨e, he, hev⟩
    · exact .inl (join_left h hv)
    · rcases List.mem_cons.mp he with rfl | hin
      · exact .inl (join_right hev hv)
      · exact .inr ⟨e, hin, hev⟩

theorem inInterval_of {lo hi x : Int} (h1 : lo ≤ x) (h2 : x ≤ hi) (h0 : 0 ≤ x) :
    inInterval lo hi x = true := by
  simp only [inInterval, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- `Load`: some environment describes the frame after loading from any address in the set. -/
theorem loadS_ok {σ : Nat → Int} {f : Frame} {st : List Int} {m : Nat → Int} {pc : Nat} {addr : Val}
    {n : Nat} (h : FrameOk σ f st m) (hx : addr.has (n : Int)) (hxI : InI64 (n : Int))
    (hmI : ∀ j, InI64 (m j)) : ∃ σ', FrameOk σ' (loadS f pc addr) (m n :: st) m := by
  have hb := boundedAddresses_has hx
  unfold loadS
  cases hc : boundedAddresses addr with
  | known xs =>
    rw [hc] at hb
    rcases xs with _ | ⟨a0, _ | ⟨a1, l⟩⟩
    · simp [Val.has] at hb
    · have ha : (n : Int) = a0 := by simpa [Val.has] using hb
      subst ha
      simp only
      have hcell : cellOk σ (f.cellOf (n : Int)) (m n) := cellOf_ok h
      split
      · rename_i hrel
        have hf := forget_ok (x := m n) pc h
        refine ⟨upd σ pc (m n), ⟨?_, ?_⟩, ?_, ?_⟩
        · exact copy_fresh_ok hcell
        · exact hf.1
        · intro e he
          rcases mem_memSet.mp he with rfl | ⟨hin, _⟩
          · refine ⟨by simp, ?_⟩
            simpa using copy_fresh_ok (pc := pc) hcell
          · exact hf.2.1 e hin
        · intro a ha
          exact hf.2.2 a (memGet_memSet_none ha).2
      · exact ⟨σ, ⟨hcell, h.1⟩, h.2⟩
    · simp only
      refine ⟨σ, ⟨cell_plain_ok ?_, h.1⟩, h.2⟩
      apply loadFold_aux (hmI n)
      refine .inl ⟨(n : Int), ?_, cellVal_has h⟩
      exact List.mem_filter.mpr ⟨hb, by simp⟩
  | range lo hi =>
    simp only
    rw [hc] at hb
    refine ⟨σ, ⟨cell_plain_ok ?_, h.1⟩, h.2⟩
    apply foldJoin_has (hmI n)
    cases hg : memGet f.mem (n : Int) with
    | none => exact .inl (h.2.2 n hg)
    | some c =>
      have hin := memGet_mem hg
      refine .inr ⟨((n : Int), c), List.mem_filter.mpr ⟨hin, ?_⟩, ?_⟩
      · exact inInterval_of hb.1 hb.2 (by omega)
      · simpa using (h.2.1 _ hin).2.1
  | unknown =>
    simp only
    refine ⟨σ, ⟨cell_plain_ok ?_, h.1⟩, h.2⟩
    apply foldJoin_has (hmI n)
    have hI : i64Min ≤ (n : Int) ∧ (n : Int) ≤ i64Max := hxI
    cases hg : memGet f.mem (n : Int) with
    | none => exact .inl (h.2.2 n hg)
    | some c =>
      have hin := memGet_mem hg
      refine .inr ⟨((n : Int), c), List.mem_filter.mpr ⟨hin, ?_⟩, ?_⟩
      · exact inInterval_of hI.1 hI.2 (by omega)
      · simpa using (h.2.1 _ hin).2.1

/-- What a fold of joins keeps. `seen` is what has been written so far. -/
def StoreGood (σ : Nat → Int) (f : Frame) (m : Nat → Int) (v : Int) (seen : List Int)
    (l : List (Int × Cell)) : Prop :=
  (∀ e ∈ l, 0 ≤ e.1 ∧
    (e.1 ∈ seen → e.2.val.has (m e.1.toNat) ∧ e.2.val.has v ∧ e.2.rel = none) ∧
    (e.1 ∉ seen → cellOk σ e.2 (m e.1.toNat))) ∧
  (∀ a : Nat, memGet l a = none → memGet f.mem a = none) ∧
  (∀ a ∈ seen, memGet l a ≠ none)

theorem memGet_of_mem_key {l : List (Int × Cell)} {a : Int} {c : Cell} (h : (a, c) ∈ l) :
    memGet l a ≠ none := fun hn => memGet_none_iff.mp hn _ h rfl

theorem storeFold_good {σ : Nat → Int} {f : Frame} {st : List Int} {m : Nat → Int} {v : Int}
    (hf : FrameOk σ f st m) (hvI : InI64 v) (hmI : ∀ j, InI64 (m j)) (hval : Val)
    (xs seen : List Int) (l : List (Int × Cell)) (hxs : ∀ a ∈ xs, 0 ≤ a)
    (hw : hval.has v) (hg : StoreGood σ f m v seen l) :
    StoreGood σ f m v (seen ++ xs) (storeFold f (.plain hval) xs l) := by
  induction xs generalizing seen l with
  | nil => simpa [storeFold] using hg
  | cons a xs ih =>
    simp only [storeFold]
    have ha0 : 0 ≤ a := hxs a (.head _)
    have hnat : ((a.toNat : Nat) : Int) = a := by omega
    generalize hold : (memGet l a).getD (Cell.plain f.rest) = old
    have hoh : old.val.has (m a.toNat) := by
      subst hold
      cases hgg : memGet l a with
      | none =>
        have h1 := hg.2.1 a.toNat (by rw [hnat]; exact hgg)
        exact hf.2.2 a.toNat h1
      | some c =>
        obtain ⟨_, h2, h3⟩ := hg.1 _ (memGet_mem hgg)
        simp only [Option.getD_some]
        by_cases hs : a ∈ seen
        · exact (h2 hs).1
        · exact (h3 hs).1
    have hrel : (old.join (Cell.plain hval)).rel = none := by
      simp only [Cell.join, Cell.plain]
      by_cases hk : old.rel = none <;> simp [hk]
    have hjoin1 : (old.join (Cell.plain hval)).val.has (m a.toNat) := join_left hoh (hmI _)
    have hjoin2 : (old.join (Cell.plain hval)).val.has v := join_right hw hvI
    have := ih (seen ++ [a]) (memSet a (old.join (Cell.plain hval)) l)
      (fun b hb => hxs b (.tail _ hb)) ?_
    · simpa [List.append_assoc] using this
    · refine ⟨?_, ?_, ?_⟩
      · intro e he
        rcases mem_memSet.mp he with rfl | ⟨hin, hne⟩
        · exact ⟨ha0, fun _ => ⟨hjoin1, hjoin2, hrel⟩, fun hn => absurd (by simp) hn⟩
        · obtain ⟨h1, h2, h3⟩ := hg.1 e hin
          refine ⟨h1, fun hs => ?_, fun hs => ?_⟩
          · rcases List.mem_append.mp hs with hs | hs
            · exact h2 hs
            · simp at hs
              exact absurd hs hne
          · exact h3 fun hc => hs (List.mem_append.mpr (.inl hc))
      · intro b hb
        exact hg.2.1 b (memGet_memSet_none hb).2
      · intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · intro hn
          obtain ⟨hne, hold'⟩ := memGet_memSet_none hn
          exact hg.2.2 b hb hold'
        · simp at hb
          subst hb
          exact memGet_of_mem_key (c := old.join (Cell.plain hval)) (mem_memSet.mpr (.inl rfl))

/-- `Store` through an interval: only listed cells in it, and `rest`, can change. -/
theorem storeOther_ok {σ : Nat → Int} {f : Frame} {st : List Int} {m : Nat → Int} {value : Cell}
    {v : Int} {n : Nat} {lo hi : Int} (h : FrameOk σ f st m) (hv : cellOk σ value v)
    (h1 : lo ≤ (n : Int)) (h2 : (n : Int) ≤ hi) (hvI : InI64 v) (hmI : ∀ j, InI64 (m j)) :
    FrameOk σ
      { f with
        mem := f.mem.map fun e => if inInterval lo hi e.1 then (e.1, e.2.join (.plain value.val)) else e
        rest := f.rest.join value.val } st (fun i => if i = n then v else m i) := by
  refine ⟨h.1, ?_, ?_⟩
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    obtain ⟨h0, hok⟩ := h.2.1 e0 he0
    by_cases hin : inInterval lo hi e0.1 = true
    · simp only [hin, ↓reduceIte]
      refine ⟨h0, ?_, ?_⟩
      · simp only [Cell.join]
        split
        · exact join_right hv.1 hvI
        · exact join_left hok.1 (hmI _)
      · simp only [Cell.join, Cell.plain]
        by_cases hk : e0.2.rel = none <;> simp [hk, relHolds]
    · simp only [hin, Bool.false_eq_true, ↓reduceIte]
      refine ⟨h0, ?_⟩
      have hne : e0.1.toNat ≠ n := by
        intro he2
        apply hin
        have : e0.1 = (n : Int) := by omega
        rw [this]
        exact inInterval_of h1 h2 (by omega)
      rw [ite_eq_right hne]
      exact hok
  · intro a ha
    have hnone : memGet f.mem a = none := by
      rw [memGet_none_iff] at ha ⊢
      intro e he
      have := ha (if inInterval lo hi e.1 then (e.1, e.2.join (.plain value.val)) else e)
        (List.mem_map.mpr ⟨e, he, rfl⟩)
      split at this <;> exact this
    simp only
    split
    · exact join_right hv.1 hvI
    · exact join_left (h.2.2 a hnone) (hmI a)

/-- `Store`: the frame after writing through any address in the set describes the new memory. -/
theorem storeS_ok {σ : Nat → Int} {f : Frame} {st : List Int} {m : Nat → Int} {value : Cell}
    {addr : Val} {v : Int} {n : Nat} (h : FrameOk σ f st m) (hv : cellOk σ value v)
    (hx : addr.has (n : Int)) (hxI : InI64 (n : Int)) (hvI : InI64 v) (hmI : ∀ j, InI64 (m j)) :
    FrameOk σ (storeS f value addr) st (fun i => if i = n then v else m i) := by
  have hb := boundedAddresses_has hx
  have hold : ∀ k : Int, 0 ≤ k → k ≠ (n : Int) → k.toNat ≠ n := by
    intro k h0 hne he
    apply hne
    omega
  unfold storeS
  cases hc : boundedAddresses addr with
  | known xs =>
    rw [hc] at hb
    rcases xs with _ | ⟨a0, _ | ⟨a1, l⟩⟩
    · simp [Val.has] at hb
    · have ha : (n : Int) = a0 := by simpa [Val.has] using hb
      subst ha
      refine ⟨h.1, ?_, ?_⟩
      · intro e he
        rcases mem_memSet.mp he with rfl | ⟨hin, hne⟩
        · refine ⟨by simp, ?_⟩
          simpa using hv
        · obtain ⟨h1, h2⟩ := h.2.1 e hin
          refine ⟨h1, ?_⟩
          simp only
          rw [ite_eq_right (hold _ h1 hne)]
          exact h2
      · intro a ha
        obtain ⟨hne, hg⟩ := memGet_memSet_none ha
        simp only
        rw [ite_eq_right (by omega)]
        exact h.2.2 a hg
    · simp only
      have hgood := storeFold_good h hvI hmI value.val
        (((a0 :: a1 :: l).filter (0 ≤ ·))) [] f.mem
        (fun a ha => by simpa using (List.mem_filter.mp ha).2) hv.1
        ⟨fun e he => ⟨(h.2.1 e he).1, fun hs => by simp at hs, fun _ => (h.2.1 e he).2⟩,
          fun _ ha => ha, fun _ ha => by simp at ha⟩
      rw [List.nil_append] at hgood
      have hnm : (n : Int) ∈ (a0 :: a1 :: l).filter (0 ≤ ·) :=
        List.mem_filter.mpr ⟨hb, by simp⟩
      refine ⟨h.1, ?_, ?_⟩
      · intro e he
        obtain ⟨h1, h2, h3⟩ := hgood.1 e he
        refine ⟨h1, ?_⟩
        by_cases hs : e.1 ∈ (a0 :: a1 :: l).filter (0 ≤ ·)
        · obtain ⟨g1, g2, g3⟩ := h2 hs
          simp only
          split
          · exact ⟨g2, by rw [g3]; trivial⟩
          · exact ⟨g1, by rw [g3]; trivial⟩
        · have hne : e.1 ≠ (n : Int) := fun he' => hs (he' ▸ hnm)
          simp only
          rw [ite_eq_right (hold _ h1 hne)]
          exact h3 hs
      · intro a ha
        have hne : a ≠ n := by
          intro he
          subst he
          exact hgood.2.2 _ hnm ha
        simp only
        rw [ite_eq_right hne]
        exact h.2.2 a (hgood.2.1 a ha)
  | range lo hi =>
    rw [hc] at hb
    exact storeOther_ok h hv hb.1 hb.2 hvI hmI
  | unknown =>
    have hI : i64Min ≤ (n : Int) ∧ (n : Int) ≤ i64Max := hxI
    exact storeOther_ok h hv hI.1 hI.2 hvI hmI

/-! ## One instruction: the next state -/

theorem allOk1 {σ : Nat → Int} {ops : List Cell} {vals : List Int} (h : AllOk σ ops vals)
    (hl : vals.length = 1) : ∃ c x, ops = [c] ∧ vals = [x] ∧ cellOk σ c x := by
  rcases vals with _ | ⟨x, _ | ⟨y, vs⟩⟩
  · simp at hl
  · rcases ops with _ | ⟨c, _ | ⟨d, cs⟩⟩
    · exact False.elim h
    · exact ⟨c, x, rfl, rfl, h.1⟩
    · exact False.elim h.2
  · simp at hl

theorem allOk2 {σ : Nat → Int} {ops : List Cell} {vals : List Int} (h : AllOk σ ops vals)
    (hl : vals.length = 2) :
    ∃ c d x y, ops = [c, d] ∧ vals = [x, y] ∧ cellOk σ c x ∧ cellOk σ d y := by
  rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, vs⟩⟩⟩
  · simp at hl
  · simp at hl
  · rcases ops with _ | ⟨c, _ | ⟨d, _ | ⟨e, cs⟩⟩⟩
    · exact False.elim h
    · exact False.elim h.2
    · exact ⟨c, d, x, y, rfl, rfl, h.1, h.2.1⟩
    · exact False.elim h.2.2
  · simp at hl

theorem allOk3 {σ : Nat → Int} {ops : List Cell} {vals : List Int} (h : AllOk σ ops vals)
    (hl : vals.length = 3) :
    ∃ c d e x y z, ops = [c, d, e] ∧ vals = [x, y, z] ∧ cellOk σ c x ∧ cellOk σ d y ∧
      cellOk σ e z := by
  rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, vs⟩⟩⟩⟩
  · simp at hl
  · simp at hl
  · simp at hl
  · rcases ops with _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨g, cs⟩⟩⟩⟩
    · exact False.elim h
    · exact False.elim h.2
    · exact False.elim h.2.2
    · exact ⟨c, d, e, x, y, z, rfl, rfl, h.1, h.2.1, h.2.2.1⟩
    · exact False.elim h.2.2.2
  · simp at hl

theorem landTo_succ {P : List Instr} {t s' : State} {x : Int} {after : Option Frame}
    {st : List Int} {m : Nat → Int} (h : jumpTo P t x = .next s') (hd : Describes after st m)
    (hs : t.stack = st) (hm : t.mem = m) : Succ (land P x after) s'.pc s'.stack s'.mem := by
  subst hs hm
  exact land_succ h hd

theorem nil_ok (σ : Nat → Int) : AllOk σ [] [] := trivial

theorem copy_succ {P : List Instr} {pc : Nat} {rest : Option Frame} {r : List Int} {m : Nat → Int}
    {σ : Nat → Int} {source : Cell} {x : Int} {t s' : State} {between : Option Cell}
    {vals : List Int} (hrest : Desc σ rest r m) (hc : cellOk σ source x)
    (hb : match between, vals with
      | some d, [y] => cellOk σ d y
      | none, [] => True
      | _, _ => False)
    (h : jumpTo P t ((pc : Int) + 1) = .next s') (hs : t.stack = x :: (vals ++ x :: r))
    (hm : t.mem = m) : Succ (copyS P pc rest source between) s'.pc s'.stack s'.mem := by
  unfold copyS
  simp only
  by_cases hf : source.rel = none
  · simp only [hf, ↓reduceIte, decide_true]
    refine landTo_succ h ?_ hs hm
    have hd := desc_mono (x := x) hrest pc
    have hcc := copy_fresh_ok (pc := pc) hc
    match between, vals, hb with
    | some d, [y], hb =>
      exact withTop_ok (vals := [x, y, x]) hd
        ⟨hcc, forgetCell_ok pc hb, hcc, trivial⟩
    | none, [], _ =>
      exact withTop_ok (vals := [x, x]) hd ⟨hcc, hcc, trivial⟩
  · simp only [hf, ↓reduceIte]
    refine landTo_succ h ?_ hs hm
    match between, vals, hb with
    | some d, [y], hb => exact withTop_ok (vals := [x, y, x]) hrest ⟨hc, hb, hc, trivial⟩
    | none, [], _ => exact withTop_ok (vals := [x, x]) hrest ⟨hc, hc, trivial⟩

theorem binaryS_succ {P : List Instr} {pc : Nat} {i : Instr} {rest : Option Frame} {r : List Int}
    {m : Nat → Int} {σ : Nat → Int} {a b : Cell} {x y rr : Int} {t s' : State}
    (hrest : Desc σ rest r m) (ha : cellOk σ a x) (hb : cellOk σ b y) (hxI : InI64 x)
    (hyI : InI64 y) (hf : binFn i x y = some rr) (hrI : InI64 rr) (hi : i = .mod → y ≠ 0)
    (h : jumpTo P t ((pc : Int) + 1) = .next s') (hs : t.stack = rr :: r) (hm : t.mem = m) :
    Succ (binaryS P pc i rest a b) s'.pc s'.stack s'.mem := by
  obtain ⟨v, hv, hvh⟩ := resultOf_has ha.1 hb.1 hxI hyI hf hrI hi
  unfold binaryS
  simp only [hv]
  apply Succ.seq_right
  exact landTo_succ h (withTop_ok (vals := [rr]) hrest ⟨⟨hvh, relate_ok ha hb hf⟩, trivial⟩) hs hm

theorem divisor_has {b : Val} {y : Int} (hb : b.has y) (hy : y ≠ 0) :
    (match b with
      | .known xs => Val.of (xs.filter (· ≠ 0))
      | other => other).has y := by
  split
  · exact of_has (List.mem_filter.mpr ⟨hb, by simpa using hy⟩)
  · exact hb

theorem divS_succ {P : List Instr} {pc : Nat} {i : Instr} {rest : Option Frame} {r : List Int}
    {m : Nat → Int} {σ : Nat → Int} {a b : Cell} {x y rr : Int} {t s' : State}
    (hrest : Desc σ rest r m) (ha : cellOk σ a x) (hb : cellOk σ b y) (hxI : InI64 x)
    (hyI : InI64 y) (hy : y ≠ 0) (hf : binFn i x y = some rr) (hrI : InI64 rr)
    (h : jumpTo P t ((pc : Int) + 1) = .next s') (hs : t.stack = rr :: r) (hm : t.mem = m) :
    Succ (divS P pc i rest a b) s'.pc s'.stack s'.mem := by
  have hgo : (checkVal .divisionByZero b.val (· ≠ 0)).2 = true :=
    checkVal_go hb.1 (by simpa using hy)
  obtain ⟨v, hv, hvh⟩ := resultOf_has ha.1 (divisor_has hb.1 hy) hxI hyI hf hrI (fun _ => hy)
  unfold divS
  simp only [hgo, ↓reduceIte, hv]
  apply Succ.seq_right
  apply Succ.seq_right
  exact landTo_succ h (withTop_ok (vals := [rr]) hrest ⟨cell_plain_ok hvh, trivial⟩) hs hm

theorem branchS_ok {rest : Option Frame} {r : List Int} {m : Nat → Int} {σ : Nat → Int} {cond : Cell}
    {c : Int} {zero : Bool} (hrest : Desc σ rest r m) (hr : ∀ v ∈ r, InI64 v)
    (hmI : ∀ j, InI64 (m j)) (hc : cellOk σ cond c) (hz : (c = 0) ↔ zero = true) :
    ∃ after, branchS rest cond zero = some after ∧ Describes after r m := by
  cases rest with
  | none => exact ⟨none, rfl, trivial⟩
  | some f =>
    have hf : FrameOk σ { f with stack := [] ++ f.stack } r m := hrest
    obtain ⟨f', hf', hok⟩ := afterBranch_ok hf hr hmI hc hz
    refine ⟨some f', ?_, ⟨σ, hok⟩⟩
    show Option.map some (Frame.afterBranch { f with stack := [] ++ f.stack } cond zero) = _
    rw [hf']
    rfl

theorem canOther_of {v : Val} {c : Int} (hv : v.has c) (hc : c ≠ 0) : canOther v = true := by
  cases v with
  | known xs => exact List.any_eq_true.mpr ⟨c, hv, by simpa using hc⟩
  | range lo hi => rfl
  | unknown => rfl

theorem condS_taken {P : List Instr} {pc : Nat} {isJz : Bool} {rest : Option Frame} {r : List Int}
    {m : Nat → Int} {σ : Nat → Int} {cond off : Cell} {c o : Int} {t s' : State}
    (hrest : Desc σ rest r m) (hr : ∀ v ∈ r, InI64 v) (hmI : ∀ j, InI64 (m j))
    (hc : cellOk σ cond c) (ho : cellOk σ off o) (hz : (c = 0) ↔ isJz = true)
    (h : jumpTo P t ((pc : Int) + o) = .next s') (hs : t.stack = r) (hm : t.mem = m) :
    Succ (condS P pc isJz rest cond off) s'.pc s'.stack s'.mem := by
  obtain ⟨after, hafter, hd⟩ := branchS_ok (zero := isJz == true) hrest hr hmI hc (by simpa using hz)
  unfold condS
  simp only
  apply Succ.seq_left
  have htaken : (if isJz then cond.val.contains 0 else canOther cond.val) = true := by
    cases isJz with
    | true =>
      have : c = 0 := hz.mpr rfl
      subst this
      simpa using contains_of_has hc.1
    | false =>
      have : c ≠ 0 := fun e => by simpa using hz.mp e
      simpa using canOther_of hc.1 this
  rw [ite_eq_left htaken, hafter]
  subst hs hm
  exact jumpS_succ ho.1 h hd

theorem condS_falls {P : List Instr} {pc : Nat} {isJz : Bool} {rest : Option Frame} {r : List Int}
    {m : Nat → Int} {σ : Nat → Int} {cond off : Cell} {c : Int} {t s' : State}
    (hrest : Desc σ rest r m) (hr : ∀ v ∈ r, InI64 v) (hmI : ∀ j, InI64 (m j))
    (hc : cellOk σ cond c) (hz : (c = 0) ↔ isJz = false)
    (h : jumpTo P t ((pc : Int) + 1) = .next s') (hs : t.stack = r) (hm : t.mem = m) :
    Succ (condS P pc isJz rest cond off) s'.pc s'.stack s'.mem := by
  obtain ⟨after, hafter, hd⟩ := branchS_ok (zero := isJz == false) hrest hr hmI hc (by simpa using hz)
  unfold condS
  simp only
  apply Succ.seq_right
  have hfalls : (if isJz then canOther cond.val else cond.val.contains 0) = true := by
    cases isJz with
    | true =>
      have : c ≠ 0 := fun e => by simpa using hz.mp e
      simpa using canOther_of hc.1 this
    | false =>
      have : c = 0 := hz.mpr rfl
      subst this
      simpa using contains_of_has hc.1
  rw [ite_eq_left hfalls, hafter]
  exact landTo_succ h hd hs hm

theorem mem_readValues {v : Int} (h : v = -1 ∨ ∃ d : Nat, d ≤ 255 ∧ v = d) : v ∈ readValues := by
  refine List.mem_map.mpr ?_
  rcases h with rfl | ⟨d, hd, rfl⟩
  · exact ⟨0, List.mem_range.mpr (by omega), by omega⟩
  · exact ⟨d + 1, List.mem_range.mpr (by omega), by omega⟩

-- Unifying through `Val.of` looks at the 257 values `READ` can push.
set_option maxRecDepth 20000 in
theorem readVal_has {v : Int} (h : v = -1 ∨ ∃ d : Nat, d ≤ 255 ∧ v = d) : readVal.has v :=
  of_has (mem_readValues h)

-- Unifying through `Val.of` looks at the 257 values `READ` can push.
set_option maxRecDepth 20000 in
theorem read_ok {σ : Nat → Int} {rest : Option Frame} {r : List Int} {m : Nat → Int} {pc : Nat}
    {v : Int} (hrest : Desc σ rest r m) (hv : v = -1 ∨ ∃ d : Nat, d ≤ 255 ∧ v = d) :
    Describes (rest.map fun f =>
      let g := f.forget pc
      { g with stack := ⟨readVal, some (.offset pc 0)⟩ :: g.stack })
      (v :: r) m := by
  cases rest with
  | none => trivial
  | some f =>
    have hf := forget_ok (x := v) pc hrest
    refine ⟨upd σ pc v, ⟨⟨readVal_has hv, by simp [relHolds, upd]⟩, hf.1⟩, hf.2.1, hf.2.2⟩

theorem mem_foldr_insertS {g : Int → Int} {xs : List Int} {x : Int} (h : x ∈ xs) :
    g x ∈ xs.foldr (fun y acc => insertS (g y) acc) [] := by
  induction xs with
  | nil => simp at h
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | hin
    · exact mem_insertS.mpr (.inl rfl)
    · exact mem_insertS.mpr (.inr (ih hin))

theorem notVal_has {a : Val} {x : Int} (h : a.has x) : (notVal a).has (b2i (x = 0)) := by
  unfold notVal
  split
  · rename_i xs
    apply of_has
    have := mem_foldr_insertS (g := fun y => if y = 0 then 1 else 0) h
    simpa [b2i] using this
  · split
    · exact b2i_either _
    · rename_i hc
      have hne : x ≠ 0 := by
        intro he
        subst he
        exact hc (contains_of_has h)
      rw [b2i_verdict_false hne]
      simp [Val.one, Val.has]

theorem notRel_ok {σ : Nat → Int} {rel : Option Rel} {x : Int} (h : relHolds σ rel x) :
    relHolds σ (notRel rel) (b2i (x = 0)) := by
  cases rel with
  | none => trivial
  | some r =>
    cases r with
    | offset s off =>
      simp only [relHolds] at h
      subst h
      simp only [notRel, relHolds, b2i, Cmp.holds]
      by_cases hz : σ s + off = 0 <;> simp [hz]
    | test s off c k =>
      simp only [relHolds] at h
      simp only [notRel, relHolds, holds_negated]
      cases hh : c.holds (σ s + off) k with
      | true =>
        simp only [hh, ↓reduceIte] at h
        subst h
        simp [b2i]
      | false =>
        simp only [hh, Bool.false_eq_true, ↓reduceIte] at h
        subst h
        simp [b2i]

/-- One instruction, next state: if the concrete operands are described and the model continues
with values in 64 bits, a successor describes where it goes, or the step gave up and said so. -/
theorem body_next {P : List Instr} {pc : Nat} {i : Instr} {rest : Option Frame} {ops : List Cell}
    {vals r : List Int} {m : Nat → Int} {inp out : List Nat} {s' : State} {σ : Nat → Int}
    (hops : AllOk σ ops vals) (hlen : vals.length = needed i) (hrest : Desc σ rest r m)
    (hst : ∀ v ∈ vals ++ r, InI64 v) (hmI : ∀ j, InI64 (m j)) (hin : ∀ x ∈ inp, x ≤ 255)
    (hs : exec P ⟨pc, vals ++ r, m, inp, out⟩ i = .next s') (hv : ∀ v ∈ s'.stack, InI64 v) :
    Succ (body P pc i rest ops) s'.pc s'.stack s'.mem := by
  have hr : ∀ v ∈ r, InI64 v := fun v h => hst v (List.mem_append.mpr (.inr h))
  have hval : ∀ v ∈ vals, InI64 v := fun v h => hst v (List.mem_append.mpr (.inl h))
  have topFits : ∀ {t : State} {x : Int} {a : Int} {l : List Int}, jumpTo P t x = .next s' →
      t.stack = a :: l → InI64 a := by
    intro t x a l hj ht
    obtain ⟨_, _, rfl⟩ := jumpTo_some hj
    exact hv a (by simp [ht])
  cases i with
  | push n =>
    have hnil : vals = [] := List.length_eq_zero_iff.mp hlen
    subst hnil
    simp only [List.nil_append, exec, advance] at hs
    exact landTo_succ hs (withTop_ok (vals := [(n.val : Int)]) hrest ⟨one_ok _, trivial⟩) rfl rfl
  | dup =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact copy_succ (between := none) (vals := []) hrest hc trivial hs rfl rfl
  | drop =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact landTo_succ hs (withTop_ok (vals := []) hrest trivial) rfl rfl
  | swap =>
    obtain ⟨b, a, y, x, rfl, rfl, hb, ha⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact landTo_succ hs (withTop_ok (vals := [x, y]) hrest ⟨ha, hb, trivial⟩) rfl rfl
  | over =>
    obtain ⟨b, a, y, x, rfl, rfl, hb, ha⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact copy_succ (between := some b) (vals := [y]) hrest ha hb hs rfl rfl
  | rot =>
    obtain ⟨c, b, a, z, y, x, rfl, rfl, hc, hb, ha⟩ := allOk3 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact landTo_succ hs (withTop_ok (vals := [x, z, y]) hrest ⟨ha, hc, hb, trivial⟩) rfl rfl
  | add | sub | mul | eq | lt | gt =>
    obtain ⟨b, a, y, x, rfl, rfl, hb, ha⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, binary, advance] at hs
    have hrI := topFits hs rfl
    exact binaryS_succ hrest ha hb (hval x (by simp)) (hval y (by simp))
      (by first | rfl | (simp only [binFn, checkedI]; rw [ite_eq_left hrI])) hrI (by simp) hs rfl rfl
  | div =>
    obtain ⟨b, a, y, x, rfl, rfl, hb, ha⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, divLike, advance] at hs
    split at hs
    · cases hs
    · rename_i hy
      have hrI := topFits hs rfl
      exact divS_succ hrest ha hb (hval x (by simp)) (hval y (by simp)) hy
        (by simp only [binFn, checkedI]; rw [ite_eq_left hrI]) hrI hs rfl rfl
  | mod =>
    obtain ⟨b, a, y, x, rfl, rfl, hb, ha⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, divLike, advance] at hs
    split at hs
    · cases hs
    · rename_i hy
      have hrI := topFits hs rfl
      exact divS_succ hrest ha hb (hval x (by simp)) (hval y (by simp)) hy rfl hrI hs rfl rfl
  | load =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    split at hs
    · cases hs
    · rename_i hx
      have hx0 : 0 ≤ x := by omega
      obtain ⟨n, rfl⟩ : ∃ n : Nat, x = n := ⟨x.toNat, by omega⟩
      have hgo : (checkVal .negativeAddress c.val (0 ≤ ·)).2 = true :=
        checkVal_go hc.1 (by simpa using hx0)
      show Succ (let k := checkVal .negativeAddress c.val (0 ≤ ·)
        if k.2 then k.1.seq (land P ((pc : Int) + 1) (rest.map fun f => loadS f pc c.val)) else k.1) _ _ _
      simp only [hgo, ↓reduceIte]
      apply Succ.seq_right
      have hd : Describes (rest.map fun f => loadS f pc c.val) (m n :: r) m := by
        cases rest with
        | none => trivial
        | some f =>
          obtain ⟨σ', h'⟩ := loadS_ok (pc := pc) hrest hc.1 (hval _ (by simp)) hmI
          exact ⟨σ', h'⟩
      rw [Int.toNat_natCast] at hs
      exact landTo_succ hs hd rfl rfl
  | store =>
    obtain ⟨c, d, x, v, rfl, rfl, hc, hd⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    split at hs
    · cases hs
    · rename_i hx
      have hx0 : 0 ≤ x := by omega
      obtain ⟨n, rfl⟩ : ∃ n : Nat, x = n := ⟨x.toNat, by omega⟩
      have hgo : (checkVal .negativeAddress c.val (0 ≤ ·)).2 = true :=
        checkVal_go hc.1 (by simpa using hx0)
      show Succ (let k := checkVal .negativeAddress c.val (0 ≤ ·)
        if k.2 then k.1.seq (land P ((pc : Int) + 1) (rest.map fun f => storeS f d c.val)) else k.1) _ _ _
      simp only [hgo, ↓reduceIte]
      apply Succ.seq_right
      have hdd : Describes (rest.map fun f => storeS f d c.val) r
          (fun i => if i = n then v else m i) := by
        cases rest with
        | none => trivial
        | some f =>
          exact ⟨σ, storeS_ok hrest hd hc.1 (hval _ (by simp)) (hval _ (by simp)) hmI⟩
      rw [Int.toNat_natCast] at hs
      exact landTo_succ hs hdd rfl rfl
  | jmp =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec] at hs
    exact jumpS_succ hc.1 hs (withTop_ok (vals := []) hrest trivial)
  | jz =>
    obtain ⟨c, d, o, x, rfl, rfl, hc, hd⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    split at hs
    · rename_i hx
      exact condS_taken hrest hr hmI hd hc (by simpa using hx) hs rfl rfl
    · rename_i hx
      exact condS_falls hrest hr hmI hd (by simpa using hx) hs rfl rfl
  | jnz =>
    obtain ⟨c, d, o, x, rfl, rfl, hc, hd⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    split at hs
    · rename_i hx
      exact condS_taken hrest hr hmI hd hc (by simpa using hx) hs rfl rfl
    · rename_i hx
      exact condS_falls hrest hr hmI hd (by simpa using hx) hs rfl rfl
  | halt =>
    cases (show Outcome.halt _ = Outcome.next s' from hs)
  | call =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec] at hs
    exact jumpS_succ hc.1 hs (withTop_ok (vals := [(pc : Int) + 1]) hrest ⟨one_ok _, trivial⟩)
  | ret =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec] at hs
    exact retS_succ hc.1 hs (withTop_ok (vals := []) hrest trivial)
  | read =>
    have hnil : vals = [] := List.length_eq_zero_iff.mp hlen
    subst hnil
    simp only [List.nil_append, exec, advance] at hs
    cases inp with
    | nil =>
      simp only at hs
      exact landTo_succ hs (read_ok hrest (.inl rfl)) rfl rfl
    | cons d l =>
      simp only at hs
      exact landTo_succ hs (read_ok hrest (.inr ⟨d, hin d (.head _), rfl⟩)) rfl rfl
  | write =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    split at hs
    · rename_i hx
      have hgo : (checkVal .invalidByte c.val fun x => decide (0 ≤ x) && decide (x ≤ 255)).2 = true :=
        checkVal_go hc.1 (by simpa using hx)
      show Succ (let k := checkVal .invalidByte c.val fun x => decide (0 ≤ x) && decide (x ≤ 255)
        if k.2 then k.1.seq (land P ((pc : Int) + 1) (withTop rest [])) else k.1) _ _ _
      simp only [hgo, ↓reduceIte]
      apply Succ.seq_right
      exact landTo_succ hs (withTop_ok (vals := []) hrest trivial) rfl rfl
    · cases hs
  | not =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact landTo_succ hs (withTop_ok (vals := [b2i (x = 0)]) hrest
      ⟨⟨notVal_has hc.1, notRel_ok hc.2⟩, trivial⟩) rfl rfl

/-! ## One instruction: faults -/

/-- The issue that foresees a model fault. A `pc` fault may also be foreseen as an unknown jump:
the report states both, and an unknown jump may land anywhere. -/
def IssueFor (f : Fault) (l : List (Kind × Bool)) : Prop :=
  match f with
  | .stackUnderflow => ∃ c, (.stackUnderflow, c) ∈ l
  | .divisionByZero => ∃ c, (.divisionByZero, c) ∈ l
  | .negativeAddress => ∃ c, (.negativeAddress, c) ∈ l
  | .invalidByte => ∃ c, (.invalidByte, c) ∈ l
  | .pcOutOfRange => ∃ c, (.pcOutOfRange, c) ∈ l ∨ (.unknownJump, c) ∈ l

theorem IssueFor.left {f : Fault} {a : List (Kind × Bool)} (b : List (Kind × Bool))
    (h : IssueFor f a) : IssueFor f (a ++ b) := by
  cases f <;> simp only [IssueFor] at h ⊢
  all_goals
    first
    | (obtain ⟨c, hc⟩ := h; exact ⟨c, List.mem_append.mpr (.inl hc)⟩)
    | (obtain ⟨c, hc | hc⟩ := h
       · exact ⟨c, .inl (List.mem_append.mpr (.inl hc))⟩
       · exact ⟨c, .inr (List.mem_append.mpr (.inl hc))⟩)

theorem IssueFor.right {f : Fault} {b : List (Kind × Bool)} (a : List (Kind × Bool))
    (h : IssueFor f b) : IssueFor f (a ++ b) := by
  cases f <;> simp only [IssueFor] at h ⊢
  all_goals
    first
    | (obtain ⟨c, hc⟩ := h; exact ⟨c, List.mem_append.mpr (.inr hc)⟩)
    | (obtain ⟨c, hc | hc⟩ := h
       · exact ⟨c, .inl (List.mem_append.mpr (.inr hc))⟩
       · exact ⟨c, .inr (List.mem_append.mpr (.inr hc))⟩)

theorem jumpTo_fault_inv {P : List Instr} {t : State} {x : Int} {f : Fault}
    (h : jumpTo P t x = .fault f) : ¬ (0 ≤ x ∧ x < (P.length : Int)) ∧ f = .pcOutOfRange := by
  unfold jumpTo at h
  split at h
  · cases h
  · rename_i hc
    exact ⟨hc, (Outcome.fault.inj h).symm⟩

theorem land_fault {P : List Instr} {t : State} {x : Int} {f : Fault} (after : Option Frame)
    (h : jumpTo P t x = .fault f) : IssueFor f (land P x after).issues := by
  obtain ⟨h1, rfl⟩ := jumpTo_fault_inv h
  unfold land
  rw [ite_eq_right h1]
  exact ⟨false, .inl (.head _)⟩

theorem fold_land_issue_mono {P : List Instr} {g : Int → Int} {after : Option Frame}
    (xs : List Int) (acc : Step) {f : Fault} (h : IssueFor f acc.issues) :
    IssueFor f (xs.foldl (fun acc o => acc.seq (land P (g o) after)) acc).issues := by
  induction xs generalizing acc with
  | nil => exact h
  | cons x l ih =>
    simp only [List.foldl_cons]
    exact ih _ (IssueFor.left _ h)

theorem fold_land_issue {P : List Instr} {g : Int → Int} {after : Option Frame} {xs : List Int}
    {o : Int} (hmem : o ∈ xs) (acc : Step) {t : State} {f : Fault}
    (h : jumpTo P t (g o) = .fault f) :
    IssueFor f (xs.foldl (fun acc o => acc.seq (land P (g o) after)) acc).issues := by
  induction xs generalizing acc with
  | nil => simp at hmem
  | cons x l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hin
    · exact fold_land_issue_mono l _ (IssueFor.right _ (land_fault after h))
    · exact ih hin _

theorem jumpS_fault {P : List Instr} {pc : Nat} {off : Val} {after : Option Frame} {o : Int}
    (ho : off.has o) {t : State} {f : Fault} (h : jumpTo P t ((pc : Int) + o) = .fault f) :
    IssueFor f (jumpS P pc off after).issues := by
  unfold jumpS
  split
  · exact fold_land_issue (g := fun o => (pc : Int) + o) ho _ h
  · obtain ⟨_, rfl⟩ := jumpTo_fault_inv h
    exact ⟨false, .inr (.head _)⟩

theorem retS_fault {P : List Instr} {addr : Val} {after : Option Frame} {a : Int}
    (ha : addr.has a) {t : State} {f : Fault} (h : jumpTo P t a = .fault f) :
    IssueFor f (retS P addr after).issues := by
  unfold retS
  split
  · exact fold_land_issue (g := fun o => o) ha _ h
  · obtain ⟨_, rfl⟩ := jumpTo_fault_inv h
    exact ⟨false, .inr (.head _)⟩

theorem condS_taken_fault {P : List Instr} {pc : Nat} {isJz : Bool} {rest : Option Frame}
    {r : List Int} {m : Nat → Int} {σ : Nat → Int} {cond off : Cell} {c o : Int} {t : State}
    {f : Fault} (hrest : Desc σ rest r m) (hr : ∀ v ∈ r, InI64 v) (hmI : ∀ j, InI64 (m j))
    (hc : cellOk σ cond c) (ho : cellOk σ off o) (hz : (c = 0) ↔ isJz = true)
    (h : jumpTo P t ((pc : Int) + o) = .fault f) :
    IssueFor f (condS P pc isJz rest cond off).issues := by
  obtain ⟨after, hafter, _⟩ := branchS_ok (zero := isJz == true) hrest hr hmI hc (by simpa using hz)
  unfold condS
  simp only
  apply IssueFor.left
  have htaken : (if isJz then cond.val.contains 0 else canOther cond.val) = true := by
    cases isJz with
    | true =>
      have : c = 0 := hz.mpr rfl
      subst this
      simpa using contains_of_has hc.1
    | false =>
      have : c ≠ 0 := fun e => by simpa using hz.mp e
      simpa using canOther_of hc.1 this
  rw [ite_eq_left htaken, hafter]
  exact jumpS_fault ho.1 h

theorem condS_falls_fault {P : List Instr} {pc : Nat} {isJz : Bool} {rest : Option Frame}
    {r : List Int} {m : Nat → Int} {σ : Nat → Int} {cond off : Cell} {c : Int} {t : State}
    {f : Fault} (hrest : Desc σ rest r m) (hr : ∀ v ∈ r, InI64 v) (hmI : ∀ j, InI64 (m j))
    (hc : cellOk σ cond c) (hz : (c = 0) ↔ isJz = false)
    (h : jumpTo P t ((pc : Int) + 1) = .fault f) :
    IssueFor f (condS P pc isJz rest cond off).issues := by
  obtain ⟨after, hafter, _⟩ := branchS_ok (zero := isJz == false) hrest hr hmI hc (by simpa using hz)
  unfold condS
  simp only
  apply IssueFor.right
  have hfalls : (if isJz then canOther cond.val else cond.val.contains 0) = true := by
    cases isJz with
    | true =>
      have : c ≠ 0 := fun e => by simpa using hz.mp e
      simpa using canOther_of hc.1 this
    | false =>
      have : c = 0 := hz.mpr rfl
      subst this
      simpa using contains_of_has hc.1
  rw [ite_eq_left hfalls, hafter]
  exact land_fault _ h

theorem binaryS_fault {P : List Instr} {pc : Nat} {i : Instr} {rest : Option Frame} {a b : Cell}
    {x y rr : Int} {t : State} {f : Fault} {σ : Nat → Int} (ha : cellOk σ a x) (hb : cellOk σ b y)
    (hxI : InI64 x) (hyI : InI64 y) (hf : binFn i x y = some rr) (hrI : InI64 rr)
    (hi : i = .mod → y ≠ 0) (h : jumpTo P t ((pc : Int) + 1) = .fault f) :
    IssueFor f (binaryS P pc i rest a b).issues := by
  obtain ⟨v, hv, _⟩ := resultOf_has ha.1 hb.1 hxI hyI hf hrI hi
  unfold binaryS
  simp only [hv]
  apply IssueFor.right
  exact land_fault _ h

theorem check_issue_div {b : Val} {σ : Nat → Int} {c : Cell} (hc : cellOk σ c 0) :
    ∃ k, (.divisionByZero, k) ∈ (checkVal .divisionByZero c.val (· ≠ 0)).1.issues := by
  have hI : InI64 0 := by
    unfold InI64 i64Min i64Max
    omega
  refine checkVal_issue hc.1 hI (by simp) ?_
  intro lo hi h1 h2
  simp only [↓reduceIte, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem divS_fault_zero {P : List Instr} {pc : Nat} {i : Instr} {rest : Option Frame} {a b : Cell}
    {σ : Nat → Int} (hb : cellOk σ b 0) :
    IssueFor .divisionByZero (divS P pc i rest a b).issues := by
  obtain ⟨k, hk⟩ := check_issue_div (b := .unknown) hb
  unfold divS
  simp only
  split
  · exact IssueFor.left _ ⟨k, hk⟩
  · exact ⟨k, hk⟩

theorem divS_fault_go {P : List Instr} {pc : Nat} {i : Instr} {rest : Option Frame} {a b : Cell}
    {x y rr : Int} {t : State} {f : Fault} {σ : Nat → Int} (ha : cellOk σ a x) (hb : cellOk σ b y)
    (hxI : InI64 x) (hyI : InI64 y) (hy : y ≠ 0) (hf : binFn i x y = some rr) (hrI : InI64 rr)
    (h : jumpTo P t ((pc : Int) + 1) = .fault f) :
    IssueFor f (divS P pc i rest a b).issues := by
  have hgo : (checkVal .divisionByZero b.val (· ≠ 0)).2 = true :=
    checkVal_go hb.1 (by simpa using hy)
  obtain ⟨v, hv, _⟩ := resultOf_has ha.1 (divisor_has hb.1 hy) hxI hyI hf hrI (fun _ => hy)
  unfold divS
  simp only [hgo, ↓reduceIte, hv]
  apply IssueFor.right
  apply IssueFor.right
  exact land_fault _ h

theorem check_issue_neg {σ : Nat → Int} {c : Cell} {x : Int} (hc : cellOk σ c x) (hI : InI64 x)
    (hx : x < 0) : ∃ k, (.negativeAddress, k) ∈ (checkVal .negativeAddress c.val (0 ≤ ·)).1.issues := by
  refine checkVal_issue hc.1 hI (by simpa using hx) ?_
  intro lo hi h1 h2
  simp only [reduceCtorEq, ↓reduceIte, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  exact .inl (by omega)

theorem check_issue_byte {σ : Nat → Int} {c : Cell} {x : Int} (hc : cellOk σ c x) (hI : InI64 x)
    (hx : ¬ (0 ≤ x ∧ x ≤ 255)) :
    ∃ k, (.invalidByte, k) ∈
      (checkVal .invalidByte c.val fun x => decide (0 ≤ x) && decide (x ≤ 255)).1.issues := by
  refine checkVal_issue hc.1 hI (by simpa using hx) ?_
  intro lo hi h1 h2
  simp only [reduceCtorEq, ↓reduceIte, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- What the bounded machine has checked before a model fault: the result fits in 64 bits. -/
def Fits : Instr → Int → Int → Prop
  | .add, x, y => InI64 (x + y)
  | .sub, x, y => InI64 (x - y)
  | .mul, x, y => InI64 (x * y)
  | .div, x, y => InI64 (Int.tdiv x y)
  | _, _, _ => True

/-- The stack is deep enough: the operands are there, so this is not an underflow. A fault of the
bounded machine in the model's sense is foreseen. `hfit` carries why arithmetic stayed in 64 bits. -/
theorem body_fault {P : List Instr} {pc : Nat} {i : Instr} {rest : Option Frame} {ops : List Cell}
    {vals r : List Int} {m : Nat → Int} {inp out : List Nat} {f : Fault} {σ : Nat → Int}
    (hops : AllOk σ ops vals) (hlen : vals.length = needed i) (hrest : Desc σ rest r m)
    (hst : ∀ v ∈ vals ++ r, InI64 v) (hmI : ∀ j, InI64 (m j))
    (hs : exec P ⟨pc, vals ++ r, m, inp, out⟩ i = .fault f)
    (hfit : ∀ x y, vals = [y, x] → Fits i x y) :
    IssueFor f (body P pc i rest ops).issues := by
  have hr : ∀ v ∈ r, InI64 v := fun v h => hst v (List.mem_append.mpr (.inr h))
  have hval : ∀ v ∈ vals, InI64 v := fun v h => hst v (List.mem_append.mpr (.inl h))
  cases i with
  | push n =>
    have hnil : vals = [] := List.length_eq_zero_iff.mp hlen
    subst hnil
    simp only [List.nil_append, exec, advance] at hs
    exact land_fault _ hs
  | dup =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact land_fault _ hs
  | drop =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact land_fault _ hs
  | swap =>
    obtain ⟨b, a, y, x, rfl, rfl, hb, ha⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact land_fault _ hs
  | over =>
    obtain ⟨b, a, y, x, rfl, rfl, hb, ha⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact land_fault _ hs
  | rot =>
    obtain ⟨c, b, a, z, y, x, rfl, rfl, hc, hb, ha⟩ := allOk3 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact land_fault _ hs
  | add | sub | mul =>
    obtain ⟨b, a, y, x, rfl, rfl, hb, ha⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, binary, advance] at hs
    have hrI := hfit x y rfl
    exact binaryS_fault ha hb (hval x (by simp)) (hval y (by simp))
      (by simp only [binFn, checkedI]; rw [ite_eq_left (show InI64 _ from hrI)]) hrI (by simp) hs
  | eq | lt | gt =>
    obtain ⟨b, a, y, x, rfl, rfl, hb, ha⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, binary, advance] at hs
    exact binaryS_fault ha hb (hval x (by simp)) (hval y (by simp)) rfl (inI64_b2i _) (by simp) hs
  | div =>
    obtain ⟨b, a, y, x, rfl, rfl, hb, ha⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, divLike, advance] at hs
    split at hs
    · rename_i hy
      subst hy
      cases hs
      exact divS_fault_zero hb
    · rename_i hy
      have hrI := hfit x y rfl
      exact divS_fault_go ha hb (hval x (by simp)) (hval y (by simp)) hy
        (by simp only [binFn, checkedI]; rw [ite_eq_left (show InI64 _ from hrI)]) hrI hs
  | mod =>
    obtain ⟨b, a, y, x, rfl, rfl, hb, ha⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, divLike, advance] at hs
    split at hs
    · rename_i hy
      subst hy
      cases hs
      exact divS_fault_zero hb
    · rename_i hy
      exact divS_fault_go ha hb (hval x (by simp)) (hval y (by simp)) hy rfl
        (inI64_tmod y (hval x (by simp))) hs
  | load =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    show IssueFor f (let k := checkVal .negativeAddress c.val (0 ≤ ·)
      if k.2 then k.1.seq (land P ((pc : Int) + 1) (rest.map fun g => loadS g pc c.val)) else k.1).issues
    split at hs
    · rename_i hx
      cases hs
      obtain ⟨k, hk⟩ := check_issue_neg hc (hval x (by simp)) hx
      simp only
      split
      · exact IssueFor.left _ ⟨k, hk⟩
      · exact ⟨k, hk⟩
    · rename_i hx
      have hgo : (checkVal .negativeAddress c.val (0 ≤ ·)).2 = true :=
        checkVal_go hc.1 (by simpa using hx)
      simp only [hgo, ↓reduceIte]
      exact IssueFor.right _ (land_fault _ hs)
  | store =>
    obtain ⟨c, d, x, v, rfl, rfl, hc, hd⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    show IssueFor f (let k := checkVal .negativeAddress c.val (0 ≤ ·)
      if k.2 then k.1.seq (land P ((pc : Int) + 1) (rest.map fun g => storeS g d c.val)) else k.1).issues
    split at hs
    · rename_i hx
      cases hs
      obtain ⟨k, hk⟩ := check_issue_neg hc (hval x (by simp)) hx
      simp only
      split
      · exact IssueFor.left _ ⟨k, hk⟩
      · exact ⟨k, hk⟩
    · rename_i hx
      have hgo : (checkVal .negativeAddress c.val (0 ≤ ·)).2 = true :=
        checkVal_go hc.1 (by simpa using hx)
      simp only [hgo, ↓reduceIte]
      exact IssueFor.right _ (land_fault _ hs)
  | jmp =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec] at hs
    exact jumpS_fault hc.1 hs
  | jz =>
    obtain ⟨c, d, o, x, rfl, rfl, hc, hd⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    split at hs
    · rename_i hx
      exact condS_taken_fault hrest hr hmI hd hc (by simpa using hx) hs
    · rename_i hx
      exact condS_falls_fault hrest hr hmI hd (by simpa using hx) hs
  | jnz =>
    obtain ⟨c, d, o, x, rfl, rfl, hc, hd⟩ := allOk2 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    split at hs
    · rename_i hx
      exact condS_taken_fault hrest hr hmI hd hc (by simpa using hx) hs
    · rename_i hx
      exact condS_falls_fault hrest hr hmI hd (by simpa using hx) hs
  | halt => cases (show Outcome.halt _ = Outcome.fault f from hs)
  | call =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec] at hs
    exact jumpS_fault hc.1 hs
  | ret =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec] at hs
    exact retS_fault hc.1 hs
  | read =>
    have hnil : vals = [] := List.length_eq_zero_iff.mp hlen
    subst hnil
    simp only [List.nil_append, exec, advance] at hs
    cases inp with
    | nil =>
      simp only at hs
      exact land_fault _ hs
    | cons d l =>
      simp only at hs
      exact land_fault _ hs
  | write =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    show IssueFor f (let k := checkVal .invalidByte c.val fun x => decide (0 ≤ x) && decide (x ≤ 255)
      if k.2 then k.1.seq (land P ((pc : Int) + 1) (withTop rest [])) else k.1).issues
    split at hs
    · rename_i hx
      have hgo : (checkVal .invalidByte c.val fun x => decide (0 ≤ x) && decide (x ≤ 255)).2 = true :=
        checkVal_go hc.1 (by simpa using hx)
      simp only [hgo, ↓reduceIte]
      exact IssueFor.right _ (land_fault _ hs)
    · rename_i hx
      cases hs
      obtain ⟨k, hk⟩ := check_issue_byte hc (hval x (by simp)) hx
      simp only
      split
      · exact IssueFor.left _ ⟨k, hk⟩
      · exact ⟨k, hk⟩
  | not =>
    obtain ⟨c, x, rfl, rfl, hc⟩ := allOk1 hops hlen
    simp only [List.cons_append, List.nil_append, exec, advance] at hs
    exact land_fault _ hs

/-! ## One step of a frame -/

theorem exec_underflow {P : List Instr} {pc : Nat} {st : List Int} {m : Nat → Int}
    {inp out : List Nat} {i : Instr} (h : st.length < needed i) :
    exec P ⟨pc, st, m, inp, out⟩ i = .fault .stackUnderflow := by
  rcases st with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> cases i <;>
    first
    | (exfalso; simp only [needed, List.length_cons, List.length_nil] at h; omega)
    | rfl

theorem allOk_length {σ : Nat → Int} {cs : List Cell} {vs : List Int} (h : AllOk σ cs vs) :
    cs.length = vs.length := by
  induction cs generalizing vs with
  | nil =>
    cases vs with
    | nil => rfl
    | cons _ _ => exact h.elim
  | cons c cs ih =>
    cases vs with
    | nil => exact h.elim
    | cons v vs => simp [ih h.2]

theorem allOk_take_drop {σ : Nat → Int} {cs : List Cell} {vs : List Int} (h : AllOk σ cs vs)
    (n : Nat) : AllOk σ (cs.take n) (vs.take n) ∧ AllOk σ (cs.drop n) (vs.drop n) := by
  induction n generalizing cs vs with
  | zero => exact ⟨by simp [AllOk], by simpa using h⟩
  | succ n ih =>
    cases cs with
    | nil =>
      cases vs with
      | nil => exact ⟨trivial, trivial⟩
      | cons _ _ => exact h.elim
    | cons c cs =>
      cases vs with
      | nil => exact h.elim
      | cons v vs =>
        have := ih h.2
        exact ⟨⟨h.1, this.1⟩, this.2⟩

theorem allOk_replicate (σ : Nat → Int) (vs : List Int) :
    AllOk σ (List.replicate vs.length (.plain .unknown)) vs := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨⟨trivial, trivial⟩, ih⟩

theorem take_length_needed {st : List Int} {n : Nat} (h : n ≤ st.length) :
    (st.take n).length = n := by
  simp [List.length_take, h]

/-- **Soundness of `transfer`, next state.** A described state that goes on, in 64 bits, is described
by a successor, or the step gave up and said so. -/
theorem transfer_next {P : List Instr} {pc : Nat} {i : Instr} {v : Option Frame} {st : List Int}
    {m : Nat → Int} {inp out : List Nat} {s' : State} (hd : Describes v st m)
    (hst : ∀ x ∈ st, InI64 x) (hmI : ∀ j, InI64 (m j)) (hin : ∀ x ∈ inp, x ≤ 255)
    (hs : exec P ⟨pc, st, m, inp, out⟩ i = .next s') (hv : ∀ x ∈ s'.stack, InI64 x) :
    Succ (transfer P pc i v) s'.pc s'.stack s'.mem := by
  have hle : needed i ≤ st.length := by
    apply Classical.byContradiction
    intro hn
    rw [exec_underflow (by omega)] at hs
    cases hs
  have hsplit : st.take (needed i) ++ st.drop (needed i) = st := List.take_append_drop _ _
  have hst' : ∀ x ∈ st.take (needed i) ++ st.drop (needed i), InI64 x := by
    rw [hsplit]
    exact hst
  have hs' : exec P ⟨pc, st.take (needed i) ++ st.drop (needed i), m, inp, out⟩ i = .next s' := by
    rw [hsplit]
    exact hs
  cases v with
  | none =>
    unfold transfer
    apply Succ.seq_right
    have hk := allOk_replicate (fun _ => 0) (st.take (needed i))
    rw [take_length_needed hle] at hk
    exact body_next hk (take_length_needed hle) trivial hst' hmI hin hs' hv
  | some f =>
    obtain ⟨σ, h1, h2⟩ := hd
    have hlen := allOk_length h1
    unfold transfer
    simp only
    rw [ite_eq_right (by omega)]
    obtain ⟨ha, hb⟩ := allOk_take_drop h1 (needed i)
    exact body_next ha (take_length_needed hle) ⟨hb, h2⟩ hst' hmI hin hs' hv

/-- **Soundness of `transfer`, faults.** A described state that faults in the bounded machine's sense
has the matching issue reported. -/
theorem transfer_fault {P : List Instr} {pc : Nat} {i : Instr} {v : Option Frame} {st : List Int}
    {m : Nat → Int} {inp out : List Nat} {f : Fault} (hd : Describes v st m)
    (hst : ∀ x ∈ st, InI64 x) (hmI : ∀ j, InI64 (m j))
    (hs : exec P ⟨pc, st, m, inp, out⟩ i = .fault f)
    (hfit : ∀ x y r, st = y :: x :: r → Fits i x y) :
    IssueFor f (transfer P pc i v).issues := by
  by_cases hlt : st.length < needed i
  · rw [exec_underflow hlt] at hs
    cases hs
    cases v with
    | none =>
      unfold transfer
      simp only
      rw [ite_eq_left (by omega)]
      exact IssueFor.left _ ⟨false, .head _⟩
    | some g =>
      obtain ⟨σ, h1, h2⟩ := hd
      have hlen := allOk_length h1
      unfold transfer
      simp only
      rw [ite_eq_left (by omega)]
      exact ⟨true, .head _⟩
  · have hle : needed i ≤ st.length := by omega
    have hsplit : st.take (needed i) ++ st.drop (needed i) = st := List.take_append_drop _ _
    have hst' : ∀ x ∈ st.take (needed i) ++ st.drop (needed i), InI64 x := by
      rw [hsplit]
      exact hst
    have hs' : exec P ⟨pc, st.take (needed i) ++ st.drop (needed i), m, inp, out⟩ i = .fault f := by
      rw [hsplit]
      exact hs
    have hfit' : ∀ x y, st.take (needed i) = [y, x] → Fits i x y := by
      intro x y he
      refine hfit x y (st.drop (needed i)) ?_
      calc st = st.take (needed i) ++ st.drop (needed i) := hsplit.symm
        _ = [y, x] ++ st.drop (needed i) := by rw [he]
        _ = y :: x :: st.drop (needed i) := rfl
    cases v with
    | none =>
      unfold transfer
      apply IssueFor.right
      have hk := allOk_replicate (fun _ => 0) (st.take (needed i))
      rw [take_length_needed hle] at hk
      exact body_fault hk (take_length_needed hle) trivial hst' hmI hs' hfit'
    | some g =>
      obtain ⟨σ, h1, h2⟩ := hd
      have hlen := allOk_length h1
      unfold transfer
      simp only
      rw [ite_eq_right (by omega)]
      obtain ⟨ha, hb⟩ := allOk_take_drop h1 (needed i)
      exact body_fault ha (take_length_needed hle) ⟨hb, h2⟩ hst' hmI hs' hfit'

theorem exec_halt_inv {P : List Instr} {s s' : State} {i : Instr} (h : exec P s i = .halt s') :
    i = .halt := by
  obtain ⟨pc, st, m, inp, out⟩ := s
  rcases st with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rcases inp with _ | ⟨d, inp⟩ <;> cases i <;>
    first
    | rfl
    | (simp only [exec, binary, divLike, advance, jumpTo] at h
       repeat' split at h
       all_goals cases h)

/-- **Soundness of `transfer`, halting.** -/
theorem transfer_halts (P : List Instr) (pc : Nat) (v : Option Frame) :
    (transfer P pc .halt v).halts = true := by
  cases v <;> simp [transfer, needed, body, Step.seq, Step.empty]

/-! ## The checker -/

theorem valCovers_sound {g f : Val} {v : Int} (h : valCovers g f = true) (hv : f.has v) :
    g.has v := by
  cases g with
  | unknown => trivial
  | known ys =>
    cases f with
    | known xs =>
      have := List.all_eq_true.mp h v hv
      simpa [Val.has] using this
    | range l u => cases h
    | unknown => cases h
  | range lo hi =>
    cases f with
    | known xs =>
      have := List.all_eq_true.mp h v hv
      simpa [Val.has] using this
    | range l u =>
      simp only [valCovers, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, h2⟩ := hv
      exact ⟨by omega, by omega⟩
    | unknown => cases h

theorem cellCovers_sound {σ : Nat → Int} {g f : Cell} {v : Int} (h : cellCovers g f = true)
    (hv : cellOk σ f v) : cellOk σ g v := by
  simp only [cellCovers, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨valCovers_sound h1 hv.1, ?_⟩
  rcases h2 with h2 | h2
  · rw [h2]
    trivial
  · rw [h2]
    exact hv.2

theorem stackCovers_sound {σ : Nat → Int} {gs fs : List Cell} {vs : List Int}
    (h : stackCovers gs fs = true) (hv : AllOk σ fs vs) : AllOk σ gs vs := by
  induction gs generalizing fs vs with
  | nil =>
    cases fs with
    | nil => exact hv
    | cons _ _ => cases h
  | cons g gs ih =>
    cases fs with
    | nil => cases h
    | cons f fs =>
      cases vs with
      | nil => exact hv.elim
      | cons v vs =>
        simp only [stackCovers, Bool.and_eq_true] at h
        exact ⟨cellCovers_sound h.1 hv.1, ih h.2 hv.2⟩

theorem frameCovers_sound {σ : Nat → Int} {g f : Frame} {st : List Int} {m : Nat → Int}
    (h : frameCovers g f = true) (hf : FrameOk σ f st m) : FrameOk σ g st m := by
  simp only [frameCovers, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨stackCovers_sound h1 hf.1, ?_, ?_⟩
  · intro e he
    obtain ⟨h0, hc⟩ := h4 e he
    refine ⟨h0, cellCovers_sound hc ?_⟩
    have : ((e.1.toNat : Nat) : Int) = e.1 := by omega
    have hk := cellOf_ok (a := e.1.toNat) hf
    rwa [this] at hk
  · intro a ha
    cases hg : memGet f.mem a with
    | none => exact valCovers_sound h2 (hf.2.2 a hg)
    | some c =>
      have hin := memGet_mem hg
      obtain ⟨_, hc⟩ := h3 _ hin
      have hcell : g.cellOf (a : Int) = .plain g.rest := by
        simp [Frame.cellOf, ha]
      simp only at hc
      rw [hcell] at hc
      have hk := (cellCovers_sound hc (hf.2.1 _ hin).2).1
      simpa [Cell.plain] using hk

theorem mem_of_lookup {l : List (Nat × Frame)} {k : Nat} {v : Frame} (h : l.lookup k = some v) :
    (k, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.lookup] at h
    split at h
    · rename_i he
      have : k = a := by simpa using he
      subst this
      cases h
      exact .head _
    · exact .tail _ (ih h)

theorem stacksCover_sound {s : Stacks} {g : Option Frame} {st : List Int} {m : Nat → Int}
    (h : stacksCover s g = true) (hd : Describes g st m) :
    ∃ v ∈ s.variants, Describes v st m := by
  have hunk : s.unknown = true → ∃ v ∈ s.variants, Describes v st m := by
    intro hu
    exact ⟨none, by simp [Stacks.variants, hu], trivial⟩
  cases g with
  | none => exact hunk h
  | some f =>
    simp only [stacksCover, Bool.or_eq_true] at h
    rcases h with h | h
    · exact hunk h
    · split at h
      · rename_i g0 hl
        obtain ⟨σ, hf⟩ := hd
        have hm : (f.stack.length, g0) ∈ s.byDepth := mem_of_lookup hl
        refine ⟨some g0, ?_, σ, frameCovers_sound h hf⟩
        simp only [Stacks.variants, List.mem_append, List.mem_map]
        exact .inl ⟨_, hm, rfl⟩
      · cases h

/-- A state is covered if what is recorded at its `pc` describes it. -/
def Covered (R : List Stacks) (s : State) : Prop :=
  ∃ v ∈ (recorded R s.pc).variants, Describes v s.stack s.mem

/-- One bounded step keeps a state covered by a checked result. -/
theorem check_step {P : List Instr} {R : List Stacks} {L : Limits} {b b' : BState}
    (hc : checkResult P R = true) (hP : (P.length : Int) ≤ i64Max)
    (hcov : Covered R b.core) (hr : InRange b.core) (hw : Within L b)
    (h : bstep P L b = .next b') : Covered R b'.core := by
  obtain ⟨hr', _, _⟩ := bstep_inv hP hr hw h
  have hstep : step P b.core = .next b'.core := by
    have := bstep_ref hP L b
    rwa [h] at this
  have hlt := step_pc_lt hstep
  obtain ⟨i, hi, hex⟩ := step_exec hstep
  have hpc : b.core.pc < P.length := by
    rcases List.getElem?_eq_some_iff.mp hi with ⟨hl, _⟩
    exact hl
  obtain ⟨v, hv, hd⟩ := hcov
  simp only [checkResult, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨_, hall⟩ := hc
  have hat := hall b.core.pc (List.mem_range.mpr hpc) v hv
  rw [hi] at hat
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hat
  obtain ⟨hnext, hwild⟩ := hat
  have hsucc := transfer_next (P := P) (pc := b.core.pc) (i := i) (v := v)
    (inp := b.core.input) (out := b.core.output) hd hr.1 hr.2.1 hr.2.2 hex hr'.1
  rcases hsucc with hw' | ⟨g, hg, hdg⟩
  · rcases hwild with hf | ht
    · rw [hw'] at hf
      cases hf
    · have hu := ht b'.core.pc (List.mem_range.mpr hlt)
      exact ⟨none, by simp [Stacks.variants, hu], trivial⟩
  · exact stacksCover_sound (hnext _ hg) hdg

/-- Everything a bounded run can reach from `State.init`, in the checked result. -/
theorem check_invariant {P : List Instr} {R : List Stacks} {L : Limits} {n : Nat} {b b' : BState}
    (hc : checkResult P R = true) (hP : (P.length : Int) ≤ i64Max) (hcov : Covered R b.core)
    (hr : InRange b.core) (hw : Within L b) (h : brun P L n b = .next b') :
    Covered R b'.core := by
  induction n generalizing b with
  | zero =>
    cases h
    exact hcov
  | succ n ih =>
    simp only [brun] at h
    cases ho : bstep P L b with
    | next b₁ =>
      rw [ho] at h
      obtain ⟨h1, h2, _⟩ := bstep_inv hP hr hw ho
      exact ih (check_step hc hP hcov hr hw ho) h1 h2 h
    | halt _ =>
      rw [ho] at h
      cases h
    | fault _ =>
      rw [ho] at h
      cases h

theorem start_covered {P : List Instr} {R : List Stacks} (hc : checkResult P R = true)
    (input : List Nat) : Covered R (BState.init input).core := by
  simp only [checkResult, Bool.and_eq_true] at hc
  have hd : Describes (some Frame.start) [] (fun _ => 0) :=
    ⟨fun _ => 0, trivial, fun e he => by simp [Frame.start] at he, fun _ _ => by
      simp [Frame.start, Val.one, Val.has]⟩
  exact stacksCover_sound hc.1 hd

theorem init_inRange {input : List Nat} (hin : ∀ x ∈ input, x ≤ 255) :
    InRange (BState.init input).core := by
  refine ⟨by simp [BState.init, State.init], fun _ => ?_, hin⟩
  simp only [BState.init, State.init, InI64, i64Min, i64Max]
  omega

theorem init_within (L : Limits) (input : List Nat) : Within L (BState.init input) :=
  ⟨Nat.zero_le _, by simp [BState.init, State.init], by simp [BState.init], fun _ _ => rfl⟩

/-- **A checked result describes every state a bounded run reaches from `State.init`.** -/
theorem reachable_covered {P : List Instr} {R : List Stacks} {L : Limits} {n : Nat}
    {input : List Nat} {b' : BState} (hc : checkResult P R = true)
    (hP : (P.length : Int) ≤ i64Max) (hin : ∀ x ∈ input, x ≤ 255)
    (h : brun P L n (BState.init input) = .next b') : Covered R b'.core :=
  check_invariant hc hP (start_covered hc input) (init_inRange hin) (init_within L input) h

theorem bexec_fits {P : List Instr} {L : Limits} {b : BState} {i : Instr} {f : Fault} {x y : Int}
    {r : List Int} (h : bexec P L b i = .fault (.model f)) (hst : b.core.stack = y :: x :: r) :
    Fits i x y := by
  cases i <;> try trivial
  all_goals
    simp only [bexec, bArith, hst] at h
    (repeat' split at h)
  all_goals first
    | assumption
    | (cases h; done)
    | (subst_vars; simp [Fits, InI64, i64Min, i64Max]; done)

/-- The last step of a bounded run that faults, kept covered up to there. -/
theorem brun_fault_issue {P : List Instr} {R : List Stacks} {L : Limits} {n : Nat} {b : BState}
    {f : Fault} (hc : checkResult P R = true) (hP : (P.length : Int) ≤ i64Max)
    (hcov : Covered R b.core) (hr : InRange b.core) (hw : Within L b)
    (hpc : b.core.pc < P.length) (h : brun P L n b = .fault (.model f)) :
    ∃ pc, IssueFor f (issuesAt P R pc) := by
  induction n generalizing b with
  | zero => cases h
  | succ n ih =>
    simp only [brun] at h
    cases ho : bstep P L b with
    | next b₁ =>
      rw [ho] at h
      obtain ⟨h1, h2, _⟩ := bstep_inv hP hr hw ho
      have hstep : step P b.core = .next b₁.core := by
        have := bstep_ref hP L b
        rwa [ho] at this
      exact ih (check_step hc hP hcov hr hw ho) h1 h2 (step_pc_lt hstep) h
    | halt _ =>
      rw [ho] at h
      cases h
    | fault g =>
      rw [ho] at h
      cases h
      obtain ⟨i, hi⟩ : ∃ i, P[b.core.pc]? = some i := ⟨P[b.core.pc], List.getElem?_eq_getElem hpc⟩
      have hstep : step P b.core = .fault f := by
        have := bstep_ref hP L b
        rwa [ho] at this
      simp only [step, hi] at hstep
      unfold bstep at ho
      split at ho
      · cases ho
      · simp only [hi] at ho
        obtain ⟨v, hv, hd⟩ := hcov
        have hfit : ∀ x y r, b.core.stack = y :: x :: r → Fits i x y := fun x y r he =>
          bexec_fits (b := { b with steps := b.steps + 1 }) ho he
        have hiss := transfer_fault (P := P) (pc := b.core.pc) (i := i) (v := v) hd hr.1 hr.2.1
          hstep hfit
        refine ⟨b.core.pc, ?_⟩
        have hsub : ∀ e ∈ (transfer P b.core.pc i v).issues, e ∈ issuesAt P R b.core.pc := by
          intro e he
          simp only [issuesAt, hi, List.mem_flatMap]
          exact ⟨v, hv, he⟩
        cases f <;> simp only [IssueFor] at hiss ⊢
        all_goals
          first
          | (obtain ⟨c, hk⟩ := hiss; exact ⟨c, hsub _ hk⟩)
          | (obtain ⟨c, hk | hk⟩ := hiss
             · exact ⟨c, .inl (hsub _ hk)⟩
             · exact ⟨c, .inr (hsub _ hk)⟩)

/-- **Corollary.** A fault of the model in a bounded run from `State.init` was reported. So if no
issue of a kind is reported, no run faults that way. -/
theorem fault_reported {P : List Instr} {R : List Stacks} {L : Limits} {n : Nat} {input : List Nat}
    {f : Fault} (hc : checkResult P R = true) (hP : (P.length : Int) ≤ i64Max) (hne : P ≠ [])
    (hin : ∀ x ∈ input, x ≤ 255) (h : brun P L n (BState.init input) = .fault (.model f)) :
    ∃ pc, IssueFor f (issuesAt P R pc) :=
  brun_fault_issue hc hP (start_covered hc input) (init_inRange hin) (init_within L input)
    (List.length_pos_iff.mpr hne) h

theorem brun_halt_reported {P : List Instr} {R : List Stacks} {L : Limits} {n : Nat} {b b' : BState}
    (hc : checkResult P R = true) (hP : (P.length : Int) ≤ i64Max) (hcov : Covered R b.core)
    (hr : InRange b.core) (hw : Within L b) (hpc : b.core.pc < P.length)
    (h : brun P L n b = .halt b') : haltsReported P R = true := by
  induction n generalizing b with
  | zero => cases h
  | succ n ih =>
    simp only [brun] at h
    cases ho : bstep P L b with
    | next b₁ =>
      rw [ho] at h
      obtain ⟨h1, h2, _⟩ := bstep_inv hP hr hw ho
      have hstep : step P b.core = .next b₁.core := by
        have := bstep_ref hP L b
        rwa [ho] at this
      exact ih (check_step hc hP hcov hr hw ho) h1 h2 (step_pc_lt hstep) h
    | fault _ =>
      rw [ho] at h
      cases h
    | halt b₂ =>
      have hstep : step P b.core = .halt b₂.core := by
        have := bstep_ref hP L b
        rwa [ho] at this
      obtain ⟨i, hi⟩ : ∃ i, P[b.core.pc]? = some i := ⟨P[b.core.pc], List.getElem?_eq_getElem hpc⟩
      simp only [step, hi] at hstep
      have he := exec_halt_inv hstep
      subst he
      obtain ⟨v, hv, _⟩ := hcov
      simp only [haltsReported, List.any_eq_true]
      refine ⟨b.core.pc, List.mem_range.mpr hpc, ?_⟩
      simp only [hi, List.any_eq_true]
      exact ⟨v, hv, transfer_halts _ _ _⟩

/-- **Corollary.** If the result reports no `halt`, no bounded run from `State.init` halts. -/
theorem no_halt_reported {P : List Instr} {R : List Stacks} {L : Limits} {n : Nat} {input : List Nat}
    {b' : BState} (hc : checkResult P R = true) (hP : (P.length : Int) ≤ i64Max) (hne : P ≠ [])
    (hin : ∀ x ∈ input, x ≤ 255) (hh : haltsReported P R = false) :
    brun P L n (BState.init input) ≠ .halt b' := by
  intro h
  have := brun_halt_reported hc hP (start_covered hc input) (init_inRange hin) (init_within L input)
    (List.length_pos_iff.mpr hne) h
  rw [hh] at this
  cases this

end Analyzer

end Emd
