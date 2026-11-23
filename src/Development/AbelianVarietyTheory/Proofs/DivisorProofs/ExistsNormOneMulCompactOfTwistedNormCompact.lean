module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwConj
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.FieldTheory.Separable
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPreimageQuadraticMapNoNullVectorsStatement
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Artinian.Module
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Topology.Algebra.Group.Units
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinMatrixReducedOfCharpolySeparable

section

@[expose] public section

open Matrix Polynomial

namespace GlobalTheory

theorem adjoin_matrix_reduced_of_charpoly_separable :
    ∀ (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K), N.charpoly.Separable →
      ∀ g ∈ Algebra.adjoin K {N}, ∀ m : ℕ, g ^ m = 0 → g = 0 := by
  intro K _ n N hsep g hg m hm
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · rw [pow_zero] at hm
    calc g = g * 1 := (mul_one g).symm
      _ = 0 := by rw [hm, mul_zero]
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hg
  obtain ⟨P, rfl⟩ := hg
  have h1 : minpoly K N ∣ P ^ m := minpoly.dvd K N (by rw [map_pow]; exact hm)
  have hs : (minpoly K N).Separable := hsep.of_dvd (Matrix.minpoly_dvd_charpoly N)
  have h2 : minpoly K N ∣ P := (hs.squarefree.dvd_pow_iff_dvd hmpos.ne').mp h1
  obtain ⟨q, hq⟩ := h2
  show aeval N P = 0
  rw [hq, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinMatrixReducedOfCharpolySeparableStatement

section

@[expose] public section

open Matrix Polynomial

theorem _root_.GlobalTheory.T.eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable : ∀ (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K), N.charpoly.Separable → ∀ g ∈ Algebra.adjoin K {N}, ∀ m : ℕ, g ^ m = 0 → g = 0 := by
  first | exact @GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable | exact GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable | (intros; apply GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedArtinianInvolutionIdempotentSplit

section

@[expose] public section

open Matrix Polynomial

namespace GlobalTheory

theorem reducedArtinian_exists_idem {R : Type} [CommRing R] [IsReduced R] [IsArtinianRing R]
    (a : R) : ∃ e b : R, e * e = e ∧ e = a * b ∧ a * e = a := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : R)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  have key : ∀ k : ℕ, a ^ n = a ^ (n + k) * y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => linear_combination ih + (-(a ^ k * y ^ k)) * hy
  have hm : a ^ (n + 1) = a ^ (n + 1 + (n + 1)) * y ^ (n + 1) := by
    linear_combination a * key (n + 1)
  refine ⟨a ^ (n + 1) * y ^ (n + 1), a ^ n * y ^ (n + 1), ?_, by ring, ?_⟩
  · linear_combination (-(y ^ (n + 1))) * hm
  · have h0 : (1 - a ^ (n + 1) * y ^ (n + 1)) * a ^ (n + 1) = 0 := by linear_combination hm
    have hnil : IsNilpotent ((1 - a ^ (n + 1) * y ^ (n + 1)) * a) := by
      refine ⟨n + 1, ?_⟩
      rw [mul_pow, pow_succ (1 - a ^ (n + 1) * y ^ (n + 1)) n, mul_assoc, h0, mul_zero]
    have := hnil.eq_zero
    linear_combination -this

theorem reducedArtinian_involution_split :
    ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) →
      ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧
        ∀ w, w * σ w = 0 → w * f = 0 := by
  intro R _ _ _ σ hσ
  let S : Set (Ideal R) := {I | ∃ e : R, e * e = e ∧ e * σ e = 0 ∧ I = Ideal.span {1 - e - σ e}}
  have hS : S.Nonempty := ⟨_, 0, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, heσ, rfl⟩, hmin⟩ := WellFounded.has_min wellFounded_lt S hS
  have hσe : σ e * σ e = σ e := by rw [← map_mul, he]
  set f := 1 - e - σ e with hfdef
  have hf : f * f = f := by linear_combination he + hσe + 2 * heσ
  have hσf : σ f = f := by simp only [hfdef, map_sub, map_one, hσ]; ring
  have hef : e * f = 0 := by linear_combination -he - heσ
  have hσef : σ e * f = 0 := by linear_combination -hσe - heσ
  refine ⟨e, f, he, hf, heσ, by ring, ?_⟩
  intro w hw
  by_contra hwf
  set w' := w * f with hw'def
  have hw'σ : w' * σ w' = 0 := by
    rw [hw'def, map_mul, hσf]; linear_combination (f * f) * hw
  obtain ⟨ε, a, hε, hεa, hw'ε⟩ := reducedArtinian_exists_idem w'
  have hεne : ε ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hw'ε; exact hwf hw'ε.symm
  have hεσ : ε * σ ε = 0 := by
    rw [hεa, map_mul]; linear_combination (a * σ a) * hw'σ
  have hw'f : w' * f = w' := by rw [hw'def, mul_assoc, hf]
  have hεf : ε * f = ε := by rw [hεa]; linear_combination a * hw'f
  have hσεf : σ ε * f = σ ε := by
    have := congrArg σ hεf; rw [map_mul, hσf] at this; exact this
  have hσε : σ ε * σ ε = σ ε := by rw [← map_mul, hε]
  have heε : e * ε = 0 := by linear_combination (-e) * hεf + ε * hef
  have heσε : e * σ ε = 0 := by linear_combination (-e) * hσεf + σ ε * hef
  have hσeε : σ e * ε = 0 := by linear_combination (-σ e) * hεf + ε * hσef
  have hmem : Ideal.span {1 - (e + ε) - σ (e + ε)} ∈ S :=
    ⟨e + ε, by linear_combination he + hε + 2 * heε,
      by rw [map_add (f := _)]; linear_combination heσ + heσε + hσeε + hεσ, rfl⟩
  apply hmin _ hmem
  have hff : f * (1 - (e + ε) - σ (e + ε)) = 1 - (e + ε) - σ (e + ε) := by
    rw [map_add (f := _)]; linear_combination hf - hεf - hσεf
  refine lt_of_le_of_ne ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨_, hff.symm⟩
  · intro hEq
    have : f ∈ Ideal.span {1 - (e + ε) - σ (e + ε)} := by
      rw [hEq]; exact Ideal.mem_span_singleton_self f
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    apply hεne
    have hεg : ε * (1 - (e + ε) - σ (e + ε)) = 0 := by
      rw [map_add (f := _)]; linear_combination -heε - hσeε - hε - hεσ
    linear_combination -hεf - ε * hc + c * hεg

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedArtinianInvolutionIdempotentSplitStatement

section

@[expose] public section

open Matrix Polynomial

theorem _root_.GlobalTheory.T.reduced_artinian_involution_idempotent_split : ∀ (R : Type) [CommRing R] [IsReduced R] [IsArtinianRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) → ∃ e f : R, IsIdempotentElem e ∧ IsIdempotentElem f ∧ e * σ e = 0 ∧ e + σ e + f = 1 ∧ ∀ w, w * σ w = 0 → w * f = 0 := by
  first | exact @GlobalTheory.reducedArtinian_involution_split | exact GlobalTheory.reducedArtinian_involution_split | (intros; apply GlobalTheory.reducedArtinian_involution_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneMulCompactOfTwistedNormCompact

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.Tw.NormOneCore

theorem exists_normOne_mul_compact : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (n : ℕ) (δ : Matrix (Fin n) (Fin n) K), GlobalTheory.Tw.Reg δ → ∀ C : Set (GL (Fin n) K), IsCompact C → ∃ D : Set (GL (Fin n) K), IsCompact D ∧ ∀ z : GL (Fin n) K, (z : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} → ∀ u ∈ C, (u : Matrix (Fin n) (Fin n) K) = (z : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (z : Matrix (Fin n) (Fin n) K) → ∃ t : GL (Fin n) K, (t : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} ∧ (t : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (t : Matrix (Fin n) (Fin n) K) = 1 ∧ ∃ d ∈ D, z = t * d := by
  intro K _ _ _ hK n δ hδ C hC
  have hu := hδ.1
  set N := GlobalTheory.Tw.nrm δ with hNdef
  set A := Algebra.adjoin K {N} with hAdef
  letI : CommRing A := Algebra.instCommRingAdjoinSingleton N
  have hA := GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hu
  have hmul := GlobalTheory.Tw.CentralizerAdjoin.adj_mul' hu
  have hsemi := GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ
  have hone := GlobalTheory.Tw.CentralizerAdjoin.adj_one' hu
  have hadd : ∀ x y : Matrix (Fin n) (Fin n) K, GlobalTheory.Tw.adj δ (x + y) = GlobalTheory.Tw.adj δ x + GlobalTheory.Tw.adj δ y :=
    fun x y => by simpa using hsemi 1 x y
  have hzero : GlobalTheory.Tw.adj δ 0 = 0 := by simp [GlobalTheory.Tw.adj]
  let σ : A →+* A :=
    { toFun := fun x => ⟨GlobalTheory.Tw.adj δ x, (hA x x.2).1⟩
      map_one' := Subtype.ext hone
      map_mul' := fun x y => by
        apply Subtype.ext
        change GlobalTheory.Tw.adj δ (x.1 * y.1) = _
        rw [hmul]
        simpa only [Subalgebra.coe_mul] using congrArg Subtype.val (mul_comm (⟨_, (hA y y.2).1⟩ : A) ⟨_, (hA x x.2).1⟩)
      map_zero' := Subtype.ext hzero
      map_add' := fun x y => Subtype.ext (hadd x.1 y.1) }
  have hσv : ∀ x : A, (σ x : Matrix (Fin n) (Fin n) K) = GlobalTheory.Tw.adj δ x := fun x => rfl
  have hσσ : ∀ x : A, σ (σ x) = x := fun x => Subtype.ext (hA x x.2).2
  haveI : IsReduced A := ⟨fun x ⟨m, hm⟩ => Subtype.ext
    (GlobalTheory.T.eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable K n N hδ.2 x x.2 m (by simpa using congrArg Subtype.val hm))⟩
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨e, f, he, hf, hes, hsum, hnull⟩ := GlobalTheory.T.reduced_artinian_involution_idempotent_split A σ hσσ

  have hse : σ e * f = 0 := by
    have h1 : σ e * σ e = σ e := by rw [← map_mul, he.eq]
    have : f = 1 - e - σ e := by rw [← hsum]; ring
    rw [this]; linear_combination (-1 : A) * h1 + (-1 : A) * hes
  have hef : e * f = 0 := by
    have : f = 1 - e - σ e := by rw [← hsum]; ring
    rw [this]; linear_combination -he.eq - hes
  have hσf : σ f = f := by
    have h := congrArg σ hsum
    rw [map_add (f := _), map_add (f := _), hσσ, map_one] at h
    linear_combination h - hsum
  letI : ContinuousStar K := ⟨(Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, hK]).continuous⟩
  have hqc : Continuous fun w : Matrix (Fin n) (Fin n) K => w * GlobalTheory.Tw.adj δ w := by
    unfold GlobalTheory.Tw.adj
    fun_prop
  have hss : σ e * σ e = σ e := by rw [← map_mul, he.eq]
  let S : Submodule K (Matrix (Fin n) (Fin n) K) :=
    Submodule.map (LinearMap.mulRight K (f : Matrix (Fin n) (Fin n) K)) (Subalgebra.toSubmodule A)
  have hhom : ∀ (c : K) (w : Matrix (Fin n) (Fin n) K),
      (c • w) * GlobalTheory.Tw.adj δ (c • w) = (c * star c) • (w * GlobalTheory.Tw.adj δ w) := by
    intro c w
    have : GlobalTheory.Tw.adj δ (c • w) = star c • GlobalTheory.Tw.adj δ w := by simpa [hzero] using hsemi c w 0
    rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hnullS : ∀ w ∈ S, w * GlobalTheory.Tw.adj δ w = 0 → w = 0 := by
    intro w hw h0
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hw
    have hx : (⟨a, ha⟩ * f : A) * σ (⟨a, ha⟩ * f) = 0 := Subtype.ext h0
    have h1 := hnull _ hx
    rw [mul_assoc, hf.eq] at h1
    exact congrArg Subtype.val h1
  obtain ⟨B1, hB1, hB1m⟩ := GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS
    ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * u) '' C)
    (hC.image (continuous_const.mul Units.continuous_val))
  obtain ⟨B2, hB2, hB2m⟩ := GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS
    ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) '' C)
    (hC.image (continuous_const.mul (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) K))))
  let φ : GL (Fin n) K × Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K →
      Matrix (Fin n) (Fin n) K × (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ := fun p =>
    ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * p.1 + p.2.1,
      MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + p.2.2))
  have hφ : Continuous φ :=
    ((continuous_const.add (continuous_const.mul (Units.continuous_val.comp continuous_fst))).add
      (continuous_fst.comp continuous_snd)).prodMk
      (MulOpposite.continuous_op.comp ((continuous_const.add
        (continuous_const.mul ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) K)).comp continuous_fst))).add
          (continuous_snd.comp continuous_snd)))
  refine ⟨Units.embedProduct _ ⁻¹' (φ '' (C ×ˢ (B1 ×ˢ B2))),
    Units.isClosedEmbedding_embedProduct.isCompact_preimage ((hC.prod (hB1.prod hB2)).image hφ), ?_⟩
  intro z hz u hu' huz
  have hzi : ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈ A := by
    rw [Matrix.coe_units_inv]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hz) (GlobalTheory.Tw.CentralizerAdjoin.inv_mem_adjoin_of_isUnit z.isUnit)
  set z' : A := ⟨z, hz⟩ with hz'
  set zi : A := ⟨_, hzi⟩ with hzi'
  have hz1 : z' * zi = 1 := Subtype.ext (Units.mul_inv z)
  have hsz1 : σ z' * σ zi = 1 := by rw [← map_mul, hz1, map_one]
  set tA : A := e * z' + σ e * σ zi + f with htA
  set tiA : A := e * zi + σ e * σ z' + f with htiA
  have hprod : tA * tiA = 1 := by
    rw [htA, htiA]
    linear_combination (z' * zi) * he.eq + e * hz1 + (z' * σ z' + σ zi * zi) * hes + (z' + zi) * hef +
      (σ zi * σ z') * hss + σ e * hsz1 + (σ zi + σ z') * hse + hf.eq + hsum
  have hprod' : tiA * tA = 1 := by rw [mul_comm]; exact hprod
  have hσt : σ tA = tiA := by
    rw [htA, htiA]; simp only [map_add (f := _), map_mul, hσσ, hσf]; ring
  let t : GL (Fin n) K := ⟨tA, tiA, congrArg Subtype.val hprod, congrArg Subtype.val hprod'⟩
  have hinvu : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * σ zi : A) : Matrix (Fin n) (Fin n) K) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [huz]
    exact congrArg Subtype.val (show (z' * σ z') * (zi * σ zi) = 1 by
      linear_combination (σ z' * σ zi) * hz1 + hsz1)
  refine ⟨t, tA.2, ?_, t⁻¹ * z, ?_, by simp⟩
  · show (tA : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ tA = 1
    rw [← hσv, hσt]; exact congrArg Subtype.val hprod
  refine ⟨(u, (z : Matrix (Fin n) (Fin n) K) * f, ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f),
    ⟨hu', hB1m _ (Submodule.mem_map.mpr ⟨z, hz, rfl⟩) ⟨u, hu', ?_⟩,
      hB2m _ (Submodule.mem_map.mpr ⟨_, hzi, rfl⟩) ⟨u, hu', ?_⟩⟩, ?_⟩
  · show (f : Matrix (Fin n) (Fin n) K) * u = ((z' * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (z' * f) : A) : Matrix (Fin n) (Fin n) K)
    rw [huz]
    exact congrArg Subtype.val (show f * (z' * σ z') = (z' * f) * σ (z' * f) by
      rw [map_mul, hσf]; linear_combination (-(z' * σ z')) * hf.eq)
  · show (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (zi * f) : A) : Matrix (Fin n) (Fin n) K)
    rw [hinvu]
    exact congrArg Subtype.val (show f * (zi * σ zi) = (zi * f) * σ (zi * f) by
      rw [map_mul, hσf]; linear_combination (-(zi * σ zi)) * hf.eq)
  · apply Prod.ext
    · show (e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K) + (z : Matrix (Fin n) (Fin n) K) * f = ((t⁻¹ * z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [huz]
      exact congrArg Subtype.val (show e + σ e * (z' * σ z') + z' * f = tiA * z' by
        rw [htiA]; linear_combination (-e) * hz1)
    · show MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f) = MulOpposite.op (((t⁻¹ * z)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [hinvu, _root_.mul_inv_rev, inv_inv, Units.val_mul]
      exact congrArg MulOpposite.op (congrArg Subtype.val (show e + σ e * (zi * σ zi) + zi * f = zi * tA by
        rw [htA]; linear_combination (-e) * hz1))
end GlobalTheory.Tw.NormOneCore
end
end
