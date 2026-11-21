module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm

theorem isTr_unique {ι : Type} [Fintype ι] {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} {g : ι → Matrix (Fin n) (Fin n) ℂ}
    {y₁ y₂ y' : Frames G} (h₁ : IsTr g y₁ y') (h₂ : IsTr g y₂ y') : y₁.1 = y₂.1 := by
  funext τ
  have hu : IsUnit (g τ).det := by
    have h := y'.2 τ
    rw [h₁ τ, Matrix.det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have e : g τ * y₁.1 τ = g τ * y₂.1 τ := by rw [← h₁ τ, ← h₂ τ]
  calc y₁.1 τ = (g τ)⁻¹ * (g τ * y₁.1 τ) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (g τ)⁻¹ * (g τ * y₂.1 τ) := by rw [e]
    _ = y₂.1 τ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

theorem jOf_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL G Pl0 T (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL] (R : RealDat (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) F Ks), IsInfFam R.θ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) → ℂ), ∃ J, JOf R j J := by
  intro B X I _ _ l Z G _ _ Pl0 T F Ks _ _ _ R _ j
  refine ⟨fun v k z' => if h : ∃ z : FrN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.R.N B.R.m - 1),
      IsTr (infM R.θ _ (rankP (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) k) z z' then j v ⟨h.choose.1, h.choose.2⟩ else 0, ?_⟩
  intro v k _ z z' hz
  have h : ∃ z : FrN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.R.N B.R.m - 1), IsTr (infM R.θ _ (rankP (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) k) z z' := ⟨z, hz⟩
  simp only [dif_pos h]
  have e := isTr_unique h.choose_spec hz
  exact congrArg (j v) (Subtype.ext e)

end GlobalTheory.AdForm
