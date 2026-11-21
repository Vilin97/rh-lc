module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterNormalizedEquivariantFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningMapIntoInducedLeft
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepresentationIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaStdMaxParab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianLatticeSplitPlaceComponentsDualStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryActionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
public import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement

@[expose] public section

noncomputable section

open MeasureTheory ValuativeRel Matrix Filter Topology

namespace GlobalTheory.KSplit

section Local

open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a a' : ℕ} {ν α β : kˣ →* ℂˣ}

theorem mapA_add {z : ℂ} {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ} (hl : IsEqv ν z l)
    {Φ Φ' : Matrix (Fin a) (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) (h' : Φ' ∈ SB _) :
    mapA a' l ν β (Φ + Φ') = mapA a' l ν β Φ + mapA a' l ν β Φ' := by
  funext x
  rw [Pi.add_apply, mapA, mapA, mapA, ← hl.1 _ (restrict_X0 (omA_mem_SB ν β 1 x h)) _ (restrict_X0 (omA_mem_SB ν β 1 x h'))]
  congr 1

theorem mapA_smul {z : ℂ} {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ} (hl : IsEqv ν z l) (c : ℂ)
    {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) : mapA a' l ν β (c • Φ) = c • mapA a' l ν β Φ := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, mapA, mapA, ← hl.2.1 c _ (restrict_X0 (omA_mem_SB ν β 1 x h))]
  congr 1
  ring

theorem mapA_omA_left {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ} (hl : IsEqv ν (((a + a' : ℕ) : ℂ) / 2) l) (g : GL (Fin a) k)
    {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) : mapA a' l ν β (omA ν β g 1 Φ) = mapA a' l ν β Φ := by
  funext x
  have hs := restrict_X0 (omA_mem_SB ν β 1 x h)
  have e : omA ν β 1 x (omA ν β g 1 Φ) = omA ν β g 1 (omA ν β 1 x Φ) := by
    rw [← omA_mul, ← omA_mul, one_mul, mul_one, one_mul, mul_one]
  rw [mapA, mapA, e, ← hl.2.2 g⁻¹ 1 _ hs, ← hl.2.1 _ _ (comp_mul_mem_SB g⁻¹ 1 hs)]
  congr 1
    Fintype.card_fin, apow_inv, Matrix.mul_assoc, neg_div, inv_one, Matrix.one_mul, one_mul]

theorem mapA_ne_zero {l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ} (hl : ∃ φ ∈ SB _, l φ ≠ 0) :
    ∃ Φ ∈ SB (Matrix (Fin a) (Fin (a + a')) k), mapA a' l ν β Φ 1 ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := hl
  have hf := frame_rel (k := k) (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))
  obtain ⟨Φ, hΦ, h⟩ := exists_extend_SB hf.1 hf.2.2.1 hf.2.2.2.2 hφ
  refine ⟨Φ, hΦ, ?_⟩
  have e : omA ν β 1 1 Φ = Φ := by funext X; simp [omA]
  rw [mapA, e, funext h]
  exact h0

theorem IsSmU.div (hα : IsSmU α) (hβ : IsSmU β) : IsSmU (α / β) := by
  refine ⟨Subgroup.isOpen_mono (H₁ := α.ker ⊓ β.ker) (fun x hx => ?_) (hα.1.inter hβ.1), fun x => ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.div_apply, hx.1, hx.2, div_one]
  · rw [MonoidHom.div_apply, Units.val_div_eq_div_val, norm_div, hα.2, hβ.2, div_one]

end Local

theorem map_eq_top {U H : Type} [AddCommGroup U] [Module ℂ U] [Group H] (S : Submodule ℂ U) (I : Submodule ℂ (H → ℂ))
    (hI : ∀ N : Submodule ℂ (H → ℂ), N ≤ I → (∀ f ∈ N, ∀ x, (fun h => f (h * x)) ∈ N) → N = ⊥ ∨ N = I)
    (p : U →ₗ[ℂ] I) (heq : ∀ φ ∈ S, ∀ x, ∃ φ₁ ∈ S, (p φ₁ : H → ℂ) = fun h => (p φ : H → ℂ) (h * x))
    (hne : ∃ φ ∈ S, p φ ≠ 0) : S.map p = ⊤ := by
  rcases hI ((S.map p).map I.subtype) (Submodule.map_subtype_le _ _) (by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩ x
    obtain ⟨φ₁, h1, h2⟩ := heq φ hφ x
    exact ⟨_, ⟨φ₁, h1, rfl⟩, h2⟩) with h | h
  · obtain ⟨φ, hφ, h0⟩ := hne
    have : (p φ : H → ℂ) ∈ (S.map p).map I.subtype := ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact absurd (Subtype.ext this) h0
  · exact Submodule.map_injective_of_injective I.injective_subtype (h.trans (Submodule.map_subtype_top I).symm)

section Adelic

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KFinLoc
open GlobalTheory.SplitFlip (omA omB)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ₁ x / χ₂ x
    exact h₁.1.div' h₂.1
  · rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E}
    {m m' : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' m') : ResEtaPow K (χ / χ') (m + m') := by
  intro u
  rw [MonoidHom.div_apply, Circle.coe_div, h u, h' u]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]

variable {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isPair_big (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_div h.chars.resβ h.chars.resα, h.weil⟩

theorem chrW_div (χ χ' : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) : chrW (χ / χ') t = chrW χ t / chrW χ' t := by
  ext x
  simp [chrW, locChar]


theorem one_mem_UAt {n : ℕ} (Y : Spc F E n) (v : Pl F) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

end Adelic

end GlobalTheory.KSplit

end
