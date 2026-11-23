module

public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.AbsProd
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaLoc
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MuProd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticLocalIdentity
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.LpolTwist

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.Regroup

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.regroup :
    UpperTheory.ConvolutionTheory.G2.Regroup := by
  intro E _ _ _ S hS g hg G
  have hG : ∀ w, G w = ∏ u ∈ hg.toFinset with
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)), g u := by
    intro w
    refine finprod_mem_eq_prod_of_inter_mulSupport_eq g ?_
    ext u
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_filter, Set.Finite.mem_toFinset,
      Function.mem_mulSupport]
    tauto
  have hne : ∀ w, G w ≠ 1 → ∃ u ∈ hg.toFinset,
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := by
    intro w hw
    by_contra hcon
    push_neg at hcon
    apply hw
    rw [hG w, Finset.filter_false_of_mem hcon, Finset.prod_empty]
  refine ⟨?_, ?_⟩
  · refine ((hg.toFinset.finite_toSet.biUnion
      (fun u _ => GlobalTheory.QNorm.finite_places_over (maximalRealSubfield E) E (u.under (𝓞 (maximalRealSubfield E)))))).subset ?_
    intro w hw
    obtain ⟨u, hu, huw⟩ := hne w hw
    exact Set.mem_biUnion (Finset.mem_coe.mpr hu) huw.symm
  · choose σ hσS hσ using fun w => (hS w).exists
    have huniq : ∀ u w, w ∈ S →
        u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → σ u = w := by
      intro u w hw h
      exact (hS u).unique ⟨hσS u, hσ u⟩ ⟨hw, h.symm⟩
    have hS' : S ∩ Function.mulSupport G =
        ((hg.toFinset.image σ : Finset (Pl E)) : Set (Pl E)) ∩ Function.mulSupport G := by
      ext w
      simp only [Set.mem_inter_iff, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨hw, hw'⟩
        obtain ⟨u, hu, huw⟩ := hne w hw'
        exact ⟨⟨u, hu, huniq u w hw huw⟩, hw'⟩
      · rintro ⟨⟨u, _, rfl⟩, hw'⟩
        exact ⟨hσS u, hw'⟩
    rw [finprod_mem_eq_prod_of_inter_mulSupport_eq G hS', finprod_eq_prod g hg,
      ← Finset.prod_fiberwise_of_maps_to (t := hg.toFinset.image σ) (g := σ)
        (fun u hu => Finset.mem_image_of_mem σ hu) g]
    refine Finset.prod_congr rfl fun w hw => ?_
    obtain ⟨u₀, _, rfl⟩ := Finset.mem_image.mp hw
    rw [hG]
    refine Finset.prod_congr (Finset.filter_congr fun u _ => ?_) fun _ _ => rfl
    constructor
    · intro h
      exact huniq u _ (hσS u₀) h
    · intro h
      rw [← h, hσ u]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProd

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.deltaProd :
    UpperTheory.ConvolutionTheory.G2.DeltaProd := by
  intro E _ _ _ hE μ e hμ S hS a b P₁ P₂ h₁ h₂ hc
  have hR : resultant P₁ P₂ ≠ 0 := Polynomial.resultant_ne_zero P₁ P₂ hc
  obtain ⟨fm, hm⟩ := UpperTheory.ConvolutionTheory.G2.muProd E μ e hμ _ hR
  obtain ⟨fa, ha⟩ := UpperTheory.ConvolutionTheory.G2.absProd E _ hR
  have fg := (fm.union fa).subset (Function.mulSupport_mul
    (fun u : Pl E => UpperTheory.ConvolutionTheory.G2.muAt μ u (resultant P₁ P₂))
    (fun u : Pl E => absHalf u (algebraMap E (u.adicCompletion E) (resultant P₁ P₂))))
  obtain ⟨fG, hG⟩ := UpperTheory.ConvolutionTheory.G2.regroup E S hS _ fg
  have hd := UpperTheory.ConvolutionTheory.G2.deltaLoc E hE μ e hμ a b P₁ P₂ h₁ h₂ hc
  simp only [hd]
  refine ⟨fG, ?_⟩
  rw [hG, finprod_mul_distrib fm fa]
  simp only [UpperTheory.ConvolutionTheory.G2.phase]
  rw [Finset.prod_mul_distrib, mul_mul_mul_comm, hm, ha, one_mul]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.EllCsr

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.ellCsr :
    UpperTheory.ConvolutionTheory.G2.EllCsr := by
  intro E _ _ _ _ n P hP
  have hcsr := GlobalTheory.CompanionTheory.EllLoc.csr_global hP
  refine ⟨fun h0 => ?_, hcsr, fun w => GlobalTheory.CompanionTheory.EllLoc.csr_at hP w⟩
  rw [h0, map_zero, C_0, zero_mul] at hcsr
  have hm : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).Monic := hP.1.map _
  exact hm.ne_zero (Polynomial.reverse_eq_zero.mp hcsr.symm)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.TermId

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finprod_termIdentity {ι : Type} (S : Set ι) (s d k : ι → ℂ) (c : ℂ) (hs : (Function.mulSupport s).Finite)
    (hd : (Function.mulSupport d).Finite) (h : ∀ w ∈ S, s w = d w * k w) (hc : (∏ᶠ w ∈ S, d w) * c = 1) :
    (S ∩ Function.mulSupport s).Finite ∧ ∏ᶠ w ∈ S, k w = c * ∏ᶠ w ∈ S, s w := by
  refine ⟨hs.inter_of_right _, ?_⟩
  have hk : (S ∩ Function.mulSupport k).Finite := by
    refine (hs.union hd).subset ?_
    rintro w ⟨hw, hkw⟩
    by_contra hn
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hn
    have := h w hw
    rw [hn.1, hn.2, one_mul] at this
    exact hkw this.symm
  rw [finprod_mem_congr rfl h, finprod_mem_mul_distrib' (hd.inter_of_right _) hk, ← mul_assoc, mul_comm c, hc, one_mul]

theorem UpperTheory.ConvolutionTheory.G2.termId :
    UpperTheory.ConvolutionTheory.G2.TermId := by
  intro E _ _ _ hE μ e hμ S hS n a b f φ hφ hM P₁ P₂ h₁ h₂ hco
  obtain ⟨hd, hc⟩ := UpperTheory.ConvolutionTheory.G2.deltaProd E hE μ e hμ S hS a b P₁ P₂ h₁ h₂ hco
  have hst := UpperTheory.ConvolutionTheory.G2.stAA E hE a b P₁ P₂ h₁ h₂
  have hc₁ := (UpperTheory.ConvolutionTheory.G2.ellCsr E hE a P₁ h₁).2.2
  have hc₂ := (UpperTheory.ConvolutionTheory.G2.ellCsr E hE b P₂ h₂).2.2
  refine finprod_termIdentity S _ _ _ _ ?_ hd ?_ hc
  · have : ∀ᶠ w : Pl E in cofinite, stTw2 a b w (atPl w P₁) (atPl w P₂) (φ w) = 1 := by
      filter_upwards [hφ, hst] with w h1 h2
      rw [h1, h2]
    exact Filter.eventually_cofinite.1 this
  · intro w hw
    refine hM w hw _ _ (h₁.1.map _) (h₂.1.map _) ?_ ?_ ?_ (hc₁ w) (hc₂ w)
    · rw [h₁.1.natDegree_map, h₁.2.1]
    · rw [h₂.1.natDegree_map, h₂.2.1]
    · rw [← Polynomial.map_mul]
      exact (h₁.2.2.1.mul h₂.2.2.1 hco).map
end
end
