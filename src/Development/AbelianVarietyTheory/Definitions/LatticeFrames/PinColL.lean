module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealOf

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

structure TwDat.Live {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) : Prop where
  inj : ∀ j, Function.Injective (ι j)
  first : Function.Surjective (ι 0)
  last : Function.Surjective (ι B.R.m)
  dead : ∀ j (hj : j + 1 ≤ B.R.m) γ, γ ∉ Set.range (ι (j + 1)) → ∀ α z, A.xi j hj α γ z = 0

def TwDat.RamL {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) (j : ℕ) (φ : ColT I l u a j) : Prop :=
  RamT j φ ∧ ∀ c, A.chOf j c ∉ Set.range (ι j) → φ c = 0

structure PinColL {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j)
    (ψ : AddChar (AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ℂ) (θ : InfFam (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))
    (x : ∀ j, DefSp ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j)) (vac : ∀ j, WO ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X (j + 1)) → ℂ) (c₀ : ℕ → ℂ)
    (kom : ∀ j, Om ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X (j + 1)))
    (dd : ∀ j, Ch j → Ch (j + 1) → WO ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X (j + 1)) →₀ ℂ)
    (w : ∀ j, Ch j → Ch (j + 1) → ℂ) (Ram : ∀ j, Set (ColT I l u a j))
    (rd : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) → ℂ) (cK : ℕ → ℂ) : Prop where
  is : A.Is
  live : A.Live ι
  om : ∀ j, j < B.R.m → IsWeilDatumO ψ _ _ (A.chr (j + 1)) (A.chr (j + 1)) (kom j)
  dat : ∀ j (hj : j + 1 ≤ B.R.m) α γ, GlobalTheory.SeeSaw.IsFinComb (dd j α γ) ∧
    IsRatDatum ψ _ _ A.e (fun z => w j α γ * A.xi j hj (ι j α) (ι (j + 1) γ) z) (vac j) (comb ψ _ _ (dd j α γ) (vac j))
  cst : ∀ j (hj : j + 1 ≤ B.R.m) α γ, (∃ z, A.xi j hj (ι j α) (ι (j + 1) γ) z ≠ 0) →
    cK j = (volLev (x j).vol (A.U j (ι j α)) : ℂ) * w j α γ * c₀ j *
      (A.chr (j + 1) (A.xr j (ι j α)) : ℂ) * (A.chr (j + 1) (A.xr (j + 1) (ι (j + 1) γ)) : ℂ)⁻¹
  ram : ∀ j, j ≤ B.R.m → ∀ φ, φ ∈ Ram j ↔ A.RamL ι j φ
  rdq : ∀ j (hj : j ≤ B.R.m) β φ y, rd j β φ y = A.rd θ j hj (ι j β) φ y

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL G Pl0 T (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL] (R : RealDat (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) F Ks) (g : GlobalTheory.Fam.Geo (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))
  (P : LevelP R.Pg (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.r ℂ) {t : T} (r : RowCh R P u g t) (k : ColCh (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

@[reducible] def clsKL (s : ℕ → ℂ)
    (J : SmT R.MX → GA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X' → FrN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.R.N B.R.m - 1) → ℂ) {Ch₀ : ℕ → Type}
    (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) : ClsK (realOf u R g s J) (tupOf R P u g t r k tl) where
  cl := fun j β => {c // A.chOf j c = ι j β}
  fin := fun j _ => letI := (I.chain l u a).clsFin j; Subtype.fintype _
  U := fun j β => A.U j (ι j β)
  chi := fun j β => A.chi j (ι j β)
  h := fun j β => A.h j (ι j β)
  val := fun _ _ ψ c z => ψ c.1 ⟨z.1, z.2⟩
  abelian₂ := fun j _ _ c c' => A.abelian₂ j c.1 c'.1

def PinChL (c₀ : ℕ → ℂ) {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j)
    (w : ∀ j, k.Ch j → k.Ch (j + 1) → ℂ) : Prop :=
  PinColL A ι R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK

structure PinTopL (UT : Subgroup (GA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X')) (ε : ℂ) : Prop where
  emb : IsEmbTop (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  lev : ∀ h, h ∈ UT ↔ g.bT⁻¹ * h * g.bT ∈ levS _ R.βX (datXP R P t)
  eT : ∀ n h β, k.eT n h β = Finsupp.single g.bT ε
  cP : k.cP = ε * (volLev g.volT UT : ℂ)

end GlobalTheory.AdForm
