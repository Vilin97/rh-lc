module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobPowRead
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
public import GroundTheory.PAdicHodge.UnramifiedClosure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeTateCharacterWeightStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WBMemLatS
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenPeriodFiniteExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenUnramifiedCharacterPeriodStatement
import GroundTheory.PAdicHodge.BdRTGalois
public import Development.WeilBound.CoreStatements.HeckeCharacterDeRham.DeRhamHeckeResults.LAdicHeckeDeRham.LAdicHeckeFields.FieldOfLeaves

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisActionPeriodProduct

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem actB_prod_periods {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l) (s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l))
    (hs : ∀ μ, μ ∈ s) (ht : ∀ μ, PrePer K χ μ (t μ))
    (g : GQ l) (hg : g ∈ GK K) (hfix : ∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), g (μ x) = μ x) :
      actB g (∏ μ ∈ s, t μ) =
        algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * ∏ μ ∈ s, t μ := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  letI : Fintype (↥K.1 →ₐ[ℚ_[l]] Om l) := minpoly.AlgHom.fintype ℚ_[l] (↥K.1) (Om l)
  have hsu : s = Finset.univ := Finset.eq_univ_iff_forall.2 hs
  set y : ↥K.1 := ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) with hy
  have hn : algebraMap ℚ_[l] (Om l) (Algebra.norm ℚ_[l] y) = ∏ μ ∈ s, μ y := by
    rw [hsu]
    exact Algebra.norm_eq_prod_embeddings ℚ_[l] (Om l) y
  have hr : algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] y) = ∏ μ ∈ s, rB l (μ y) := by
    rw [← map_prod, ← hn]
    exact ((GroundTheory.PAdicHodge.algClToBdR l).commutes _).symm
  rw [map_prod, hr, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun μ _ => (ht μ).2.1 g hg (hfix μ)

end GlobalTheory.CompanionTheory.LTPer
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisActionPeriodProductStatement

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.galois_action_period_product : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l) (s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l)),
    (∀ μ, μ ∈ s) → (∀ μ, PrePer K χ μ (t μ)) →
    ∀ (g : GQ l) (hg : g ∈ GK K), (∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), g (μ x) = μ x) →
      actB g (∏ μ ∈ s, t μ) =
        algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * ∏ μ ∈ s, t μ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.actB_prod_periods | exact GlobalTheory.CompanionTheory.LTPer.actB_prod_periods | (intros; apply GlobalTheory.CompanionTheory.LTPer.actB_prod_periods <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodProductFiltrationLevels

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem prod_eq_t_mul_unit_count : ∀ {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (t : ι → Formalism.Per6.BdRp l) (i₀ : ι), i₀ ∈ s →
    ∀ u : (Formalism.Per6.BdRp l)ˣ, ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l * (u : Formalism.Per6.BdRp l) →
      thB l (t i₀) = 0 →
      ∀ μ ∈ s, (μ = i₀ → t μ ∉ FB l 2) ∧ (μ ≠ i₀ → t μ ∉ FB l 1) := by
  intro l _ ι s t i₀ hi₀ u hprod h0 μ hμ
  have hmax : IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) = Ideal.span {GroundTheory.PAdicHodge.tBdR l} :=
    GroundTheory.PAdicHodge.maximalIdeal_eq_span_fontaineT GroundTheory.PAdicHodge.untilt_epsilon
      GroundTheory.PAdicHodge.untilt_frobeniusEquiv_symm_epsilon_ne_one
  have htirr : Irreducible (GroundTheory.PAdicHodge.tBdR l) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2 hmax
  have hFB : ∀ k, FB l k = Ideal.span {GroundTheory.PAdicHodge.tBdR l ^ k} := fun k => by
    rw [FB, ker_thB_eq, hmax, Ideal.span_singleton_pow]
  have hnot : ¬ (GroundTheory.PAdicHodge.tBdR l ^ 2 ∣ ∏ μ ∈ s, t μ) := by
    rw [hprod, pow_two]
    intro h
    have h1 : GroundTheory.PAdicHodge.tBdR l ∣ (u : Formalism.Per6.BdRp l) :=
      (mul_dvd_mul_iff_left htirr.ne_zero).1 h
    exact htirr.not_isUnit (isUnit_of_dvd_unit h1 u.isUnit)
  have hi : GroundTheory.PAdicHodge.tBdR l ∣ t i₀ := by
    have : t i₀ ∈ FB l 1 := by
      rw [FB, pow_one, RingHom.mem_ker]; exact h0
    rw [hFB, pow_one] at this
    exact Ideal.mem_span_singleton.1 this
  refine ⟨fun e hm => hnot ?_, fun hne hm => hnot ?_⟩
  · subst e
    rw [hFB] at hm
    exact (Ideal.mem_span_singleton.1 hm).trans (Finset.dvd_prod_of_mem t hμ)
  · rw [hFB, pow_one] at hm
    have hd := Ideal.mem_span_singleton.1 hm
    have hμ' : μ ∈ s.erase i₀ := Finset.mem_erase.2 ⟨hne, hμ⟩
    rw [← Finset.mul_prod_erase s t hi₀, ← Finset.mul_prod_erase (s.erase i₀) t hμ', pow_two, ← mul_assoc]
    exact (mul_dvd_mul hi hd).mul_right _

end GlobalTheory.CompanionTheory.LTPer
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodProductFiltrationLevelsStatement

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.period_product_filtration_levels : ∀ {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (t : ι → Formalism.Per6.BdRp l) (i₀ : ι), i₀ ∈ s →
    ∀ u : (Formalism.Per6.BdRp l)ˣ, ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l * (u : Formalism.Per6.BdRp l) →
      thB l (t i₀) = 0 →
      ∀ μ ∈ s, (μ = i₀ → t μ ∉ FB l 2) ∧ (μ ≠ i₀ → t μ ∉ FB l 1) := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.prod_eq_t_mul_unit_count | exact GlobalTheory.CompanionTheory.LTPer.prod_eq_t_mul_unit_count | (intros; apply GlobalTheory.CompanionTheory.LTPer.prod_eq_t_mul_unit_count <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTatePeriodNotFiltered

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem exact_degrees_of_product : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ),
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    ∀ t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l, (∀ μ, PrePer K χ μ (t μ)) →
      ∀ μ, (μ = K.1.val → t μ ∉ FB l 2) ∧ (μ ≠ K.1.val → t μ ∉ FB l 1) := by
  intro l _ K χ hN t ht
  haveI hfK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  obtain ⟨L, hLdef⟩ : ∃ L : IntermediateField ℚ_[l] (Om l),
      L = IntermediateField.normalClosure ℚ_[l] ↥K.1 (Om l) := ⟨_, rfl⟩
  haveI : FiniteDimensional ℚ_[l] ↥L := by
    subst hLdef
    infer_instance
  have hμL : ∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), μ x ∈ L := fun μ x => by
    subst hLdef
    exact μ.fieldRange_le_normalClosure ⟨x, rfl⟩
  have hKL : ∀ x ∈ K.1, x ∈ L := fun x hx => hμL K.1.val ⟨x, hx⟩
  let res : Gal(Om l/↥L) → GQ l := fun σ => σ.restrictScalars ℚ_[l]
  have hresv : ∀ (σ : Gal(Om l/↥L)) (y : ↥L), res σ y = y := fun σ y => σ.commutes y
  have hres : ∀ σ, res σ ∈ GK K := fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => hresv σ ⟨x, hKL x hx⟩
  obtain ⟨s, hs⟩ : ∃ s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l), ∀ μ, μ ∈ s :=
    ⟨(Set.toFinite (Set.univ : Set (↥K.1 →ₐ[ℚ_[l]] Om l))).toFinset, fun μ => by simp⟩
  have hT0 : (∏ μ ∈ s, t μ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun μ _ => (ht μ).1
  have htirr : Irreducible (GroundTheory.PAdicHodge.tBdR l) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2
      (GroundTheory.PAdicHodge.maximalIdeal_eq_span_fontaineT GroundTheory.PAdicHodge.untilt_epsilon
        GroundTheory.PAdicHodge.untilt_frobeniusEquiv_symm_epsilon_ne_one)
  obtain ⟨n, u, hTu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hT0 htirr
  have hTu' : ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l) := by
    rw [hTu, mul_comm]
  have hcyc : ∀ σ : Gal(Om l/↥L),
      (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot (res σ)) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) =
        (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun σ => by
    have h1 := GroundTheory.PAdicHodge.gal_smul_fontaineT σ (GroundTheory.PAdicHodge.untilt_epsilon (p := l))
    have h2 := GroundTheory.PAdicHodge.gal_smul_fontaineT (Formalism.Per6.toBot (res σ))
      (GroundTheory.PAdicHodge.untilt_epsilon (p := l))
    have h3 := h2.symm.trans h1
    exact (algebraMap ℚ_[l] (Formalism.Per6.BdRp l)).injective (mul_right_cancel₀ htirr.ne_zero h3)
  have hn : n = 1 := GlobalTheory.T.hodge_tate_character_weight L (GlobalTheory.T.sen_period_finite_extension GlobalTheory.T.sen_unramified_character_period L) u n
    (fun σ => Algebra.norm ℚ_[l] ((χ ⟨res σ, hres σ⟩ : (↥K.1)ˣ) : ↥K.1))
    (fun σ => by
      rw [← hTu']
      exact GlobalTheory.T.galois_action_period_product K χ t s hs ht (res σ) (hres σ) fun μ x => hresv σ ⟨μ x, hμL μ x⟩)
    (fun σ hσ => (hN (res σ) (hres σ) hσ).trans (hcyc σ))
  subst hn
  intro μ
  exact GlobalTheory.T.period_product_filtration_levels s t K.1.val (hs _) u (by rw [hTu', pow_one]) ((ht _).2.2 rfl) μ (hs μ)

end GlobalTheory.CompanionTheory.LTPer
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTatePeriodNotFilteredStatement

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.lubin_tate_period_not_filtered : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ),
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    ∀ t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l, (∀ μ, PrePer K χ μ (t μ)) →
      ∀ μ, (μ = K.1.val → t μ ∉ FB l 2) ∧ (μ ≠ K.1.val → t μ ∉ FB l 1) := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.exact_degrees_of_product | exact GlobalTheory.CompanionTheory.LTPer.exact_degrees_of_product | (intros; apply GlobalTheory.CompanionTheory.LTPer.exact_degrees_of_product <;> assumption)
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.HeckeLAdicCharacters.Outright

section

@[expose] public section

namespace HodgeLocalDeRhamField.HLdR

theorem field_outright : GlobalTheory.Published.HeckeLAdicCharacterDeRham :=
  PositivityTheory.SecR.Hladr2.field_of_leaves @GlobalTheory.CompanionTheory.LTPer.Tilt.tilt_period @GlobalTheory.T.lubin_tate_period_not_filtered

end HodgeLocalDeRhamField.HLdR
end
end
