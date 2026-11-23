module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisMatrixMapCancelLeftStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonRelationMapPrismHomStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopesAdicTopologicalBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOrientedPrismUniformizerFrameBreuilKisinHomStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproductStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonMatrixMul

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

theorem mem_nonZeroDivisors_of_associated' {R : Type} [CommRing R] {a b : R} (h : Associated a b)
    (ha : a ∈ nonZeroDivisors R) : b ∈ nonZeroDivisors R := by
  obtain ⟨v, rfl⟩ := h
  exact mul_mem_nonZeroDivisors.mpr ⟨ha, v.isUnit.mem_nonZeroDivisors⟩

theorem mul_cancel_of_rel {R : Type} [CommRing R] {n : Type} [Fintype n] {N : ℕ} {ef eg eh : R}
    (hg : eg ∈ nonZeroDivisors R) (hh : eh ∈ nonZeroDivisors R) {Pf Pg Ph ε₁ ε₂ ε₃ : Matrix n n R}
    (r1 : eg ^ N • (Pf * ε₁) = ef ^ N • Pg) (r2 : eh ^ N • (Pg * ε₂) = eg ^ N • Ph)
    (r3 : eh ^ N • (Pf * ε₃) = ef ^ N • Ph) : Pf * (ε₁ * ε₂) = Pf * ε₃ := by
  have key : (eg ^ N * eh ^ N) • (Pf * (ε₁ * ε₂)) = (eg ^ N * eh ^ N) • (Pf * ε₃) := by
    calc (eg ^ N * eh ^ N) • (Pf * (ε₁ * ε₂))
        = eh ^ N • ((eg ^ N • (Pf * ε₁)) * ε₂) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = eh ^ N • ((ef ^ N • Pg) * ε₂) := by rw [r1]
      _ = ef ^ N • (eh ^ N • (Pg * ε₂)) := by
          rw [Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
      _ = ef ^ N • (eg ^ N • Ph) := by rw [r2]
      _ = eg ^ N • (ef ^ N • Ph) := by rw [smul_smul, smul_smul, mul_comm]
      _ = eg ^ N • (eh ^ N • (Pf * ε₃)) := by rw [r3]
      _ = (eg ^ N * eh ^ N) • (Pf * ε₃) := by rw [smul_smul]
  have hc : eg ^ N * eh ^ N ∈ nonZeroDivisors R :=
    mul_mem_nonZeroDivisors.mpr ⟨pow_mem hg _, pow_mem hh _⟩
  ext i j
  have e := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at e
  exact (mul_cancel_left_mem_nonZeroDivisors hc).mp e

theorem rel_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g h : Hom bk.prism B) (ε₁ ε₂ ε₃ : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε₁ → ht.Rel (BK.hf f₀ X) g h ε₂ → ht.Rel (BK.hf f₀ X) f h ε₃ → ε₁ * ε₂ = ε₃ := by
  intro l _ K bk d ρ τ s ht B f₀ h0 f g h ε₁ ε₂ ε₃ h1 h2 h3
  have hn : ∀ k : Hom bk.prism B, ‖toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf k X)‖ ≤ bk.ρ₀ := fun k =>
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ k).1
  have hE : ∀ k : Hom bk.prism B,
      toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf k bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := fun k =>
    mem_nonZeroDivisors_of_associated' ((GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f₀ k).2.1.map (toDisc l (BK.hf f₀ X) bk.ρ₀)) h0
  have mf := isDiscMap_map (BK.hf f) (hn f)
  have mg := isDiscMap_map (BK.hf g) (hn g)
  have mh := isDiscMap_map (BK.hf h) (hn h)
  have hF : Disc.map (BK.hf f) (hn f) (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈
      nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := by
    rw [mf.ext]; exact hE f
  exact GlobalTheory.T.basis_matrix_map_cancel_left l K bk d ρ τ s ht (Disc l (BK.hf f₀ X) bk.ρ₀) _ hF _ _
    (mul_cancel_of_rel (hE g) (hE h) (h1 _ _ mf mg) (h2 _ _ mg mh) (h3 _ _ mf mh))

end GlobalTheory.BSP.Height
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonMatrixMulStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.discPeriod_comparison_matrix_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g h : Hom bk.prism B) (ε₁ ε₂ ε₃ : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε₁ → ht.Rel (BK.hf f₀ X) g h ε₂ → ht.Rel (BK.hf f₀ X) f h ε₃ → ε₁ * ε₂ = ε₃ := by
  first | exact @GlobalTheory.BSP.Height.rel_mul | exact GlobalTheory.BSP.Height.rel_mul | (intros; apply GlobalTheory.BSP.Height.rel_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinCoproductUnitCocycleIdentities

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem height_rel_unit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A),
    ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) →
    ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f₀) bk.J ι →
    (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧
    ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl →
      k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  intro l _ K bk d ρ τ s ht En ε hε B f₀ ι tb
  have H := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f₀) ι tb
  have hinj := H.1
  have hE := H.2.1
  have key : ∀ k : Hom En.Q B, ht.Rel (BK.hf f₀ X) (k.comp En.inl) (k.comp En.inr)
      ((ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := by
    intro k
    have H2 := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht En.Q B En.inl En.inl En.inr f₀ k (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    refine H2.1.elim fun Fk hFk => ?_
    have h := H2.2
    have e : (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk =
        (ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀) := Matrix.ext fun i j => hFk.ext (ε i j)
    exact e ▸ h Fk hFk
  have inj : ∀ M N : Matrix (Fin d) (Fin d) B.A, M.map (toDisc l (BK.hf f₀ X) bk.ρ₀) =
      N.map (toDisc l (BK.hf f₀ X) bk.ρ₀) → M = N := fun M N h =>
    Matrix.ext fun i j => hinj (congrFun (congrFun h i) j)
  have tr : ∀ (f f' g g' : Hom bk.prism B) (M : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)),
      f = f' → g = g' → ht.Rel (BK.hf f₀ X) f g M → ht.Rel (BK.hf f₀ X) f' g' M := fun _ _ _ _ _ hf hg h =>
    hf ▸ hg ▸ h
  refine ⟨fun k hk => ?_, fun k₁ k₂ k₃ h₁ h₂ h₃ => ?_⟩
  · have h : ht.Rel (BK.hf f₀ X) (k.comp En.inr) (k.comp En.inr)
        ((ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ hk rfl (key k)
    have e := GlobalTheory.T.discPeriod_comparison_matrix_mul l K bk d ρ τ s ht B f₀ hE _ _ _ 1 1 _ (ht.rel_one _ _) (ht.rel_one _ _) h
    exact inj _ _ ((e.symm.trans (mul_one 1)).trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)
  · have e1 : ht.Rel (BK.hf f₀ X) (k₁.comp En.inl) (k₂.comp En.inl)
        ((ε.map k₁.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ rfl h₁ (key k₁)
    have e3 : ht.Rel (BK.hf f₀ X) (k₁.comp En.inl) (k₂.comp En.inr)
        ((ε.map k₃.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ h₂.symm h₃.symm (key k₃)
    have e := GlobalTheory.T.discPeriod_comparison_matrix_mul l K bk d ρ τ s ht B f₀ hE _ _ _ _ _ _ e1 (key k₂) e3
    exact inj _ _ (Matrix.map_mul.trans e)

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinCoproductUnitCocycleIdentitiesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinCoproduct_unit_cocycle_identities : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A), ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) → ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f₀) bk.J ι → (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  first | exact @GlobalTheory.BSP.height_rel_unit_cocycle | exact GlobalTheory.BSP.height_rel_unit_cocycle | (intros; apply GlobalTheory.BSP.height_rel_unit_cocycle <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinComparisonUnitCocycleEveryPrism

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.StratCocycle

variable {l : ℕ} {R : Type} [CommRing R]

theorem comp_assoc {P P' P'' P''' : Obj l R} (h : Hom P'' P''') (g : Hom P' P'') (f : Hom P P') :
    (h.comp g).comp f = h.comp (g.comp f) := Hom.ext' rfl

theorem comp_id {P P' : Obj l R} (f : Hom P P') : f.comp (Hom.id P) = f := Hom.ext' rfl

theorem map_comp {P P' P'' : Obj l R} {d : ℕ} (ε : Matrix (Fin d) (Fin d) P.A) (g : Hom P' P'') (f : Hom P P') :
    ε.map (g.comp f).f = (ε.map f.f).map g.f := by
  rw [Matrix.map_map]; rfl

theorem unit_of_codiag {P Q B : Obj l R} {d : ℕ} (inl inr : Hom P Q)
    (univ : ∀ (C : Obj l R) (f g : Hom P C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g)
    (ε : Matrix (Fin d) (Fin d) Q.A)
    (h1 : ∀ Δ : Hom Q P, Δ.comp inl = Δ.comp inr → ε.map Δ.f = 1)
    (k : Hom Q B) (hk : k.comp inl = k.comp inr) : ε.map k.f = 1 := by
  obtain ⟨Δ, ⟨hΔl, hΔr⟩, -⟩ := univ P (Hom.id _) (Hom.id _)
  have hk' : k = (k.comp inl).comp Δ := by
    refine (univ B (k.comp inl) (k.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp (k.comp inl)) hΔl).trans (comp_id _))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp (k.comp inl)) hΔr).trans ((comp_id _).trans hk))
  calc ε.map k.f = ε.map ((k.comp inl).comp Δ).f := congrArg (fun k : Hom Q B => ε.map k.f) hk'
    _ = (ε.map Δ.f).map (k.comp inl).f := map_comp ε _ Δ
    _ = (1 : Matrix (Fin d) (Fin d) P.A).map (k.comp inl).f :=
        congrArg (fun M : Matrix (Fin d) (Fin d) P.A => M.map (k.comp inl).f) (h1 Δ (hΔl.trans hΔr.symm))
    _ = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem cocycle_of_triple {P Q Q₂ B : Obj l R} {d : ℕ} (inl inr : Hom P Q)
    (univ : ∀ (C : Obj l R) (f g : Hom P C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g)
    (i₁ : Hom Q Q₂) (j : Hom P Q₂)
    (univ₂ : ∀ (C : Obj l R) (f : Hom Q C) (g : Hom P C), ∃! h : Hom Q₂ C, h.comp i₁ = f ∧ h.comp j = g)
    (ε : Matrix (Fin d) (Fin d) Q.A)
    (hc : ∀ k₂₃ k₁₃ : Hom Q Q₂, i₁.comp inr = k₂₃.comp inl → i₁.comp inl = k₁₃.comp inl →
      k₂₃.comp inr = k₁₃.comp inr → ε.map i₁.f * ε.map k₂₃.f = ε.map k₁₃.f)
    (k₁ k₂ k₃ : Hom Q B) (h12 : k₁.comp inr = k₂.comp inl) (h13 : k₁.comp inl = k₃.comp inl)
    (h23 : k₂.comp inr = k₃.comp inr) : ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  obtain ⟨k₂₃, ⟨h₂₃l, h₂₃r⟩, -⟩ := univ Q₂ (i₁.comp inr) j
  obtain ⟨k₁₃, ⟨h₁₃l, h₁₃r⟩, -⟩ := univ Q₂ (i₁.comp inl) j
  have hc' := hc k₂₃ k₁₃ h₂₃l.symm h₁₃l.symm (h₂₃r.trans h₁₃r.symm)
  obtain ⟨m, ⟨hml, hmr⟩, -⟩ := univ₂ B k₁ (k₂.comp inr)
  have e₂ : k₂ = m.comp k₂₃ := by
    refine (univ B (k₂.comp inl) (k₂.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₂₃l).trans
        ((comp_assoc _ _ _).symm.trans ((congrArg (fun q => Hom.comp q inr) hml).trans h12)))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₂₃r).trans hmr)
  have e₃ : k₃ = m.comp k₁₃ := by
    refine (univ B (k₃.comp inl) (k₃.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₁₃l).trans
        ((comp_assoc _ _ _).symm.trans ((congrArg (fun q => Hom.comp q inl) hml).trans h13)))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₁₃r).trans (hmr.trans h23))
  subst e₂ e₃ hml
  rw [map_comp ε m i₁, map_comp ε m k₂₃, map_comp ε m k₁₃, ← Matrix.map_mul, hc']

theorem unit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A),
    ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) →
    ∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧
      ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl →
        k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  intro l _ K bk d ρ τ s ht En ε hrel B
  have cocB := GlobalTheory.T.breuilKisinCoproduct_unit_cocycle_identities l K bk d ρ τ s ht En ε hrel
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  refine ⟨unit_of_codiag En.inl En.inr En.univ ε
    (fun Δ h => (cocB bk.prism (Hom.id _) Unit (TopBasis.self bk.J)).1 Δ h), fun k₁ k₂ k₃ h12 h13 h23 => ?_⟩
  exact (GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk En.Q _ _ (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk En.Q En.inl)).elim fun En₂ =>
    (GlobalTheory.T.breuilKisinEnvelopes_adicTopologicalBasis l K bk En En₂).2.elim fun ι htb => htb.elim fun tb =>
      cocycle_of_triple En.inl En.inr En.univ En₂.inl En₂.inr En₂.univ ε
        (fun k₂₃ k₁₃ a b c => (cocB En₂.Q (En₂.inl.comp En.inl) ι tb).2 En₂.inl k₂₃ k₁₃ a b c)
        k₁ k₂ k₃ h12 h13 h23

end GlobalTheory.BSP.StratCocycle
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinComparisonUnitCocycleEveryPrismStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_comparison_unit_cocycle_every_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A), ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) → ∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  first | exact @GlobalTheory.BSP.StratCocycle.unit_cocycle | exact GlobalTheory.BSP.StratCocycle.unit_cocycle | (intros; apply GlobalTheory.BSP.StratCocycle.unit_cocycle <;> assumption)
end
end
