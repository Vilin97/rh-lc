module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

def JetS (ψ : AddChar (AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ℂ) (θ : InfFam (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (s : ℕ → ℂ) : Prop :=
  ∀ j (hj : j + 1 ≤ B.R.m), s j ≠ 0 ∧ ∀ f, IsHol θ ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X (j + 1)) ψ f → ∀ P,
    pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 =
      jetP _ _ (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j (Nat.le_of_succ_le hj)) (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (j + 1) hj) (s j) (ColDat.xiS θ j hj f) P

def lowOf : (FrN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.R.N B.R.m) → ℂ) →ₗ[ℂ] (FrN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.R.N B.R.m - 1) → ℂ) :=
  fnOf _ (shiftOf (sgT (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u)) 1 ∘ₗ (I.perIn u I.mu0).br B.fields.emb B.embLL (B.hcW u) ∘ₗ
    Formalism.L2.Col.polOf _ (shiftOf (Formalism.L2.Forms.lamT (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u B.R.m)) ⟨fun _ => 1, fun _ => by simp⟩

variable {I l Z} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL G Pl0 T (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL] (R : RealDat (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) F Ks) (g : GlobalTheory.Fam.Geo (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))

@[reducible] def realOf (s : ℕ → ℂ)
    (J : SmT R.MX → GA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X' → FrN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.R.N B.R.m - 1) → ℂ) : RealD (commOf R u g) where
  N := B.R.N
  hN := rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)
  NT := B.R.N B.R.m - 1
  hT := rankP (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)
  fr := fun _ => ⟨fun y => ⟨y.1, y.2⟩, fun y => ⟨y.1, y.2⟩, fun _ => rfl, fun _ => rfl⟩
  lam := Formalism.L2.Forms.lamT (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u
  n := fun j τ => (shiftOf (Formalism.L2.Forms.lamT (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u j) τ + (I.chain l u I.mu0).sSharp j τ).toNat
  sS := (I.chain l u I.mu0).sSharp
  sD := (I.chain l u I.mu0).sDiv
  sc := fun j τ => if s j = 0 then 1 else s j / I.J.cD τ
  BT := fun _ => 1
  sg := sgT (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u
  J := J
  low := fun _ h => Eq.rec (motive := fun n _ => (FrN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.R.N n) → ℂ) →ₗ[ℂ] (FrN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.R.N B.R.m - 1) → ℂ))
    (lowOf I l Z u) h.symm

def JOf (j : SmT R.MX →ₗ[ℂ] (FrP (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) → ℂ))
    (J : SmT R.MX → GA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X' → FrN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.R.N B.R.m - 1) → ℂ) : Prop :=
  ∀ v, ∀ k ∈ GinfC (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X', ∀ z z' : FrN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.R.N B.R.m - 1),
    IsTr (infM R.θ _ (rankP (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) k) z z' → J v k z' = j v ⟨z.1, z.2⟩

variable (P : LevelP R.Pg (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.r ℂ) {t : T} (r : RowCh R P u g t) {a : I.ι} (k : ColCh (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

end GlobalTheory.AdForm
