module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AdmissibleOfPiDecomposition
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PhiKOfNil
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilRho
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilWeil
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPhiKNil
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PWdModel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleOfCrystalline

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDvdOfNil

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.dvdOfNil_of :
    DvdOfNil := by
  classical
  intro K W _ _ _ _ _ M s u hu hnil
  obtain ⟨n, hn⟩ := hnil
  have hroot : ∀ r ∈ (LinearMap.charpoly M).roots, r ∈ s := by
    intro r hr
    have hev : M.HasEigenvalue r := (Module.End.hasEigenvalue_iff_isRoot_charpoly M r).2
      ((Polynomial.mem_roots (LinearMap.charpoly_monic M).ne_zero).1 hr)
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := Module.End.aeval_apply_of_hasEigenvector
      (p := (Polynomial.C u * rootPol s) ^ n) hv
    rw [map_pow, hn, LinearMap.zero_apply] at h1
    have h2 : ((Polynomial.C u * rootPol s) ^ n).eval r = 0 :=
      (smul_eq_zero.1 h1.symm).resolve_right hv.2
    rw [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C] at h2
    have h3 : (rootPol s).eval r = 0 :=
      (mul_eq_zero.1 (pow_eq_zero_iff'.1 h2).1).resolve_left hu
    unfold rootPol at h3
    rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map] at h3
    obtain ⟨a, ha, hra⟩ := Multiset.mem_map.1 h3
    simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hra
    rw [sub_eq_zero.1 hra]
    exact ha
  set m := (LinearMap.charpoly M).roots.card with hm
  refine ⟨m, ?_⟩
  have hcp : ((LinearMap.charpoly M).roots.map fun a => Polynomial.X - Polynomial.C a).prod
      = LinearMap.charpoly M :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (LinearMap.charpoly_monic M)
      IsAlgClosed.card_roots_eq_natDegree
  have hpow : rootPol s ^ m = ((m • s).map fun a => Polynomial.X - Polynomial.C a).prod := by
    unfold rootPol
    rw [Multiset.map_nsmul, Multiset.prod_nsmul]
  rw [← hcp, hpow]
  apply Multiset.prod_dvd_prod_of_le
  apply Multiset.map_le_map
  rw [Multiset.le_iff_count]
  intro a
  rw [Multiset.count_nsmul]
  by_cases ha : a ∈ (LinearMap.charpoly M).roots
  · have hs : 1 ≤ s.count a := Multiset.one_le_count_iff_mem.2 (hroot a ha)
    calc (LinearMap.charpoly M).roots.count a ≤ m := Multiset.count_le_card _ _
      _ = m * 1 := (mul_one m).symm
      _ ≤ m * s.count a := Nat.mul_le_mul_left m hs
  · rw [Multiset.count_eq_zero.2 ha]
    exact Nat.zero_le _
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhi

section

@[expose] public section

theorem UpperTheory.Ru.crystallineComparison.nilToPhi :
    UpperTheory.Ru.crystallineComparison.NilToPhi := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r LL r' hm hcr Q hN s u hu hQ
  refine ⟨(GlobalTheory.Pst.IsModel.isCrysAt_iff P hm).2 hcr, ?_⟩
  exact UpperTheory.Gal.crystallineComparison.phiKNil_of UpperTheory.Gal.crystallineComparison.dvdOfNil_of UpperTheory.Gal.crystallineComparison.nilWeil_of
    UpperTheory.Gal.crystallineComparison.nilRho_of UpperTheory.Gal.crystallineComparison.wdModel_of l P AI hT ι E Ω A w h O Bw hj a r LL r' hm hcr
    Q hN s u hu hQ
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiStepOf

section

@[expose] public section

private theorem UpperTheory.Ru.crystallineComparison.isGr_comp {Γ Γ' L : Type} [Group Γ] [Group Γ'] [Field L] {d : ℕ}
    {ρ₀ ρ : Γ →* GL (Fin d) L} (f : Γ' →* Γ) (h : UpperTheory.Gal.Int.Geo.IsGr ρ₀ ρ) :
    UpperTheory.Gal.Int.Geo.IsGr (ρ₀.comp f) (ρ.comp f) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun g => hc (f g)⟩

theorem UpperTheory.Ru.crystallineComparison.phiStep_of :
    UpperTheory.Ru.crystallineComparison.GeoSide → UpperTheory.Gal.Int.Geo.PhiStep := by
  intro hGeo E Ω _ _ _ _ _ l _ ι H θ hN dd ρ hc hP w hw n ϑ R hcong hR
  obtain ⟨ρ₀, hmat, hgr⟩ := hP
  obtain ⟨h0, hroot⟩ := hR
  intro P AI hT A hA O _ _ _ Bw hj
  have hcr := hGeo E Ω l H θ hN dd ρ₀ hmat w hw n ϑ hcong P AI hT A hA O Bw hj
  have hcont : Continuous (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    hc.comp continuous_subtype_val
  obtain ⟨LL, r', ϑ', hmod, hcrE, hag, hnil⟩ :=
    UpperTheory.Ru.crystallineComparison.joinQ l P AI hT E Ω _ O Bw _ _ n ϑ dd _ _ hcont
      (UpperTheory.Ru.crystallineComparison.isGr_comp _ hgr) hcr
  refine UpperTheory.Ru.crystallineComparison.nilToPhi l P AI hT ι E Ω A w hA O Bw hj dd _ LL r' hmod hcrE _ hnil R (ι (ϑ 0))
    ((map_ne_zero ι).2 h0) ?_
  rw [← hroot, UpperTheory.Gal.crystallineComparison.heckePol_map, UpperTheory.Gal.crystallineComparison.heckePol_map]
  unfold UpperTheory.Gal.crystallineComparison.heckePol
  refine Finset.sum_congr rfl fun j hj' => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj')
  simp only [RingHom.comp_apply]
  have := hag j hjn
  rw [show algebraMap ↥LL.1 (Formalism.ConjugateSelfDual.Qbar l) (ϑ' j) = ϑ j from this]
end
end
