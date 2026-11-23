module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumCoefficientFunctionalLinearDegree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumFunctionalKillsComplexCombinationsStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProofStatement
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Discriminant
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LenAtEqZeroOfSubsingleton

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumCoefficientFunctionalLinearDegreeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.arcDatum_coefficientFunctional_linear_degree : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∃ φ : sec Xo c a' n →ₗ[c.F] K₁, ∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧ ∀ F ∈ sec Xo c a' n, cfOf d.yF d.μ d.jj F ≠ 0 → ∑ v, d.μ v = absA Dw a' := by
  first | exact @GlobalTheory.ArcCM.cfOf_linear_and_degree | exact GlobalTheory.ArcCM.cfOf_linear_and_degree | (intros; apply GlobalTheory.ArcCM.cfOf_linear_and_degree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallEmbeddingSumEqZero

section

@[expose] public section

namespace GlobalTheory

theorem eq_zero_of_forall_embedding_sum_eq_zero :
    ∀ (K K₁ : Type) [Field K] [CharZero K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁] (σ₀ : K →+* ℂ) (n : ℕ) (e : Fin n → ℂ) (y : Fin n → K₁), (∀ c : Fin n → K, ∑ b, σ₀ (c b) * e b = 0 → c = 0) → (∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap K K₁) = σ₀ → ∑ b, e b * σ₁ (y b) = 0) → y = 0 := by
  intro K K₁ _ _ _ _ _ σ₀ n e y hind hrel
  classical
  letI : Algebra K ℂ := σ₀.toAlgebra
  have hσ : ∀ x : K, algebraMap K ℂ x = σ₀ x := fun _ => rfl
  let ω := Module.finBasis K K₁
  have hcard : Fintype.card (Fin (Module.finrank K K₁)) = Fintype.card (K₁ →ₐ[K] ℂ) := by
    rw [AlgHom.card, Fintype.card_fin]
  let ε : Fin (Module.finrank K K₁) ≃ (K₁ →ₐ[K] ℂ) := Fintype.equivOfCardEq hcard
  have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two K ℂ ω ε
  have hd0 : Algebra.discr K ω ≠ 0 := Algebra.discr_not_zero_of_basis K ω
  have hdet : (Algebra.embeddingsMatrixReindex K ℂ ω ε).det ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hd
    exact hd0 ((algebraMap K ℂ).injective (by rw [hd, map_zero]))
  let u : Fin (Module.finrank K K₁) → ℂ := fun s => ∑ b, σ₀ (ω.repr (y b) s) * e b
  have hu : u = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    funext j
    have h1 := hrel (ε j : K₁ →+* ℂ) (by
      ext x
      simp [hσ])
    have h2 : ∀ b, (ε j : K₁ →+* ℂ) (y b) = ∑ s, σ₀ (ω.repr (y b) s) * ε j (ω s) := by
      intro b
      conv_lhs => rw [← ω.sum_repr (y b)]

      simp only [RingHom.coe_coe, map_sum, Algebra.smul_def, map_mul, AlgHom.commutes, hσ]
    simp only [h2, Finset.mul_sum] at h1
    rw [Finset.sum_comm] at h1
    simp only [Matrix.vecMul, dotProduct, u, Finset.sum_mul, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun b _ => ?_
    have : Algebra.embeddingsMatrixReindex K ℂ ω ε s j = ε j (ω s) := by
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
    rw [this]; ring
  funext b
  apply ω.repr.injective
  ext s
  have := congrFun (hind (fun b => ω.repr (y b) s) (congrFun hu s)) b
  simpa using this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsBasisOverEmbedding

section

@[expose] public section

namespace GlobalTheory

theorem exists_basis_over_embedding (K : Type) [Field K] (σ₀ : K →+* ℂ) (m : ℕ)
    (a : Fin m → ℂ) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (c : Fin m → Fin n → K),
      (∀ t : Fin n → K, ∑ b, σ₀ (t b) * e b = 0 → t = 0) ∧
        ∀ i, a i = ∑ b, σ₀ (c i b) * e b := by
  letI : Algebra K ℂ := σ₀.toAlgebra
  have hs : ∀ (k : K) (z : ℂ), k • z = σ₀ k * z := fun k z => rfl
  let V : Submodule K ℂ := Submodule.span K (Set.range a)
  haveI : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range a)
  let B := Module.finBasis K V
  have ha : ∀ i, a i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Module.finrank K V, fun b => (B b : ℂ), fun i b => B.repr ⟨a i, ha i⟩ b, ?_, ?_⟩
  · intro t ht
    have hli := Fintype.linearIndependent_iff.1 B.linearIndependent t
    funext b
    refine hli ?_ b
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, hs, Submodule.coe_zero]
    exact ht
  · intro i
    have h := congrArg (Subtype.val : V → ℂ) (B.sum_repr ⟨a i, ha i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hs] at h
    exact h.symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormsVanishingLowCoeffSpannedByRational

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ArcCM

theorem exists_regroup_vectors {K : Type} [Field K] (σ₀ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module K M] {m : ℕ}
    (a : Fin m → ℂ) (F : Fin m → M) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (G : Fin n → M),
      (∀ r : M → ℂ, (∀ x y, r (x + y) = r x + r y) → (∀ (c : K) x, r (c • x) = σ₀ c * r x) →
        ∑ i, a i * r (F i) = ∑ b, e b * r (G b)) ∧
      ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (y : Fin n → K₁),
        (∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap K K₁) = σ₀ → ∑ b, e b * σ₁ (y b) = 0) → ∀ b, y b = 0 := by
  obtain ⟨n, e, c, hind, ha⟩ := GlobalTheory.exists_basis_over_embedding K σ₀ m a
  refine ⟨n, e, fun b => ∑ i, c i b • F i, ?_, ?_⟩
  · intro r hadd hsm
    have hs : ∀ b, r (∑ i, c i b • F i) = ∑ i, σ₀ (c i b) * r (F i) := fun b => by
      have := map_sum (AddMonoidHom.mk' r hadd) (fun i => c i b • F i) Finset.univ
      simp only [AddMonoidHom.mk'_apply, hsm] at this
      exact this
    simp only [hs, ha, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring
  · intro K₁ _ _ _ y hy b
    haveI : CharZero K := σ₀.charZero
    haveI : FiniteDimensional K K₁ := Module.Finite.of_restrictScalars_finite ℚ K K₁
    exact congrFun (GlobalTheory.eq_zero_of_forall_embedding_sum_eq_zero K K₁ σ₀ n e y hind hy) b

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.Shares


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem mggOnto_of_detect_fun : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (Fm : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁], ((recB h.toLawsCore).Cusp j ka → K₁) → Prop), (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (φ (F i)) = 0) → (∀ F : (recB h.toLawsCore).Cusp j ka, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → φ F = 0) → F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt cc j ka) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  intro D T h j ka CR Tt cc Fm hkill hdet hon f hf
  obtain ⟨m, a, F, -, hF⟩ := hon f fun k => (hf k).1
  obtain ⟨n, e, G, h1, h2⟩ := exists_regroup_vectors (K := T.Q.c.F) T.σ₀ a F
  have hG : ∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ b, e b * rdR h j (G b) k x := by
    intro k x hx
    rw [hF k x hx]
    refine h1 (fun P => rdR h j P k x) (fun P Q => ?_) (fun c P => ?_)
    · exact congrFun (congrFun (map_add (rdU (T.U j T.σ₀)) P.1 Q.1) k) x
    · exact congrFun (congrFun (map_smulₛₗ (rdU (T.U j T.σ₀)) c P.1) k) x
  refine ⟨n, e, G, fun b => hdet (G b) ?_, hG⟩
  intro K₁ _ _ _ d hd
  exact h2 K₁ (fun b => d (G b))
    (fun σ₁ hσ => hkill K₁ d hd σ₁ hσ n e G f hf hG) b


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem mggOnto_of_detect : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (Fm : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁], ((recB h.toLawsCore).Cusp j ka → K₁) → Prop), (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → IsLinearMap T.Q.c.F φ ∧ ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (φ (F i)) = 0) → (∀ F : (recB h.toLawsCore).Cusp j ka, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → φ F = 0) → F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt cc j ka) → RdOnto h j ka → MggOnto h j CR Tt cc ka :=
  fun D T h j ka CR Tt cc Fm hkill =>
    mggOnto_of_detect_fun D T h j ka CR Tt cc Fm fun K₁ _ _ _ φ hφ => (hkill K₁ φ hφ).2

end GlobalTheory.ArcCM
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormsVanishingLowCoeffSpannedByRationalStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.forms_vanishing_low_coeff_spanned_by_rational : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (Fm : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁], ((recB h.toLawsCore).Cusp j ka → K₁) → Prop), (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → IsLinearMap T.Q.c.F φ ∧ ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (φ (F i)) = 0) → (∀ F : (recB h.toLawsCore).Cusp j ka, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → φ F = 0) → F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt cc j ka) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  exact @GlobalTheory.ArcCM.mggOnto_of_detect
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.VanishingLowCoefficientReadingsSpanModels

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

namespace GlobalTheory.ConjKill


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isLinearMap_cfOf {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (K₁ : Type) [Field K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) :
    IsLinearMap T.Q.c.F fun F : (recB h).Cusp j ka => cfOf d.yF d.μ d.jj F.1 := by
  obtain ⟨φ, hφ⟩ := (GlobalTheory.T.arcDatum_coefficientFunctional_linear_degree GlobalTheory.T.arithmeticCMKnownTheorems_proof _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d (wtA ka) ka.n).1
  have hle : ∀ F : (recB h).Cusp j ka, F.1 ∈ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n := fun F =>
    cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j ka F.2)
  have e : ∀ F : (recB h).Cusp j ka, cfOf d.yF d.μ d.jj F.1 = φ ⟨F.1, hle F⟩ := fun F => (hφ ⟨F.1, hle F⟩).symm
  refine ⟨fun F G => ?_, fun a F => ?_⟩
  · rw [e, e, e, ← map_add (f := _)]; rfl
  · rw [e, e, ← map_smul]; rfl




theorem mggOnto_of_rdOnto : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), (j < D.R.m → DetectQ h.toLawsCore j ka CR Tt cc) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  intro D T h j hj ka CR Tt cc hD hR
  by_cases hlt : j < D.R.m
  · refine GlobalTheory.T.forms_vanishing_low_coeff_spanned_by_rational D T h j ka CR Tt cc
      (fun K₁ _ _ _ φ => ∃ d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁, FamQ T.toCore j ka CR Tt cc K₁ d ∧
        φ = fun F => cfOf d.yF d.μ d.jj F.1) ?_ ?_ hR
    · rintro K₁ _ _ _ φ ⟨d, hd, rfl⟩
      exact ⟨isLinearMap_cfOf h.toLawsCore j ka K₁ d, GlobalTheory.T.arcDatum_functional_kills_complexCombinations D T h j hj ka CR Tt cc K₁ d hd⟩
    · intro F hF
      exact hD hlt F fun K₁ _ _ _ d hd => hF K₁ _ ⟨d, hd, rfl⟩
  · have hρ : WeightFamilies.rho D j = 0 := by
      unfold WeightFamilies.rho Ranks.sigW
      exact Nat.sub_eq_zero_of_le (not_lt.1 hlt)
    intro f hf
    obtain ⟨m, a, F, -, hF⟩ := hR f fun k => (hf k).1
    refine ⟨m, a, F, fun i => ?_, hF⟩
    rw [SetLike.mem_coe, Formalism.MainNotions.Gaps.EtaleWeightGaps.MggK_eq_top_of_rho hρ]
    trivial

end GlobalTheory.ConjKill
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.VanishingLowCoefficientReadingsSpanModelsStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

theorem _root_.GlobalTheory.T.vanishing_low_coefficient_readings_span_models : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), (j < D.R.m → DetectQ h.toLawsCore j ka CR Tt cc) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  first | exact @GlobalTheory.ConjKill.mggOnto_of_rdOnto | exact GlobalTheory.ConjKill.mggOnto_of_rdOnto | (intros; apply GlobalTheory.ConjKill.mggOnto_of_rdOnto <;> assumption)
end
end
