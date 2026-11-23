module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomLatticeCommensurableOrthonormal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValues
public import Mathlib.NumberTheory.NumberField.Basic
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
public import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPrincipalIdealRingLoc
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingLoc

section

@[expose] public section

namespace GlobalTheory.CoprimeBasisExistence

open NumberField nonZeroDivisors

def coprimeSet (A : Type*) [CommRing A] (m : ℕ) : Submonoid A where
  carrier := {x | ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧ (k : A) = x}
  one_mem' := ⟨1, one_pos, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, ha', rfl⟩ ⟨b, hb, hb', rfl⟩
    exact ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', by simp⟩

theorem coprimeSet_le (A : Type*) [CommRing A] [IsDomain A] [CharZero A] (m : ℕ) :
    coprimeSet A m ≤ A⁰ := by
  rintro _ ⟨k, hk, _, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hk.ne')

theorem mem_of_natCast_mem {R : Type*} [CommRing R] (m : ℕ)
    (hu : ∀ k : ℕ, 0 < k → k.Coprime m → IsUnit (k : R)) (P : Ideal R) (hP : P.IsPrime) :
    ∀ n : ℕ, 0 < n → (n : R) ∈ P → (m : R) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnP
    by_cases hc : n.Coprime m
    · exact absurd hnP (fun h => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu n hn hc)))
    · have hg0 : 0 < Nat.gcd n m := Nat.gcd_pos_of_pos_left m hn
      have hg1 : 1 < Nat.gcd n m := by
        rw [Nat.Coprime] at hc
        omega
      have hn' : n = Nat.gcd n m * (n / Nat.gcd n m) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)).symm
      have hmul : ((Nat.gcd n m : R) * ((n / Nat.gcd n m : ℕ) : R)) ∈ P := by
        rw [← Nat.cast_mul, ← hn']
        exact hnP
      rcases hP.mem_or_mem hmul with h1 | h1
      · obtain ⟨c, hc'⟩ := Nat.gcd_dvd_right n m
        have e : (m : R) = (Nat.gcd n m : R) * (c : R) := by
          rw [← Nat.cast_mul, ← hc']
        rw [e]
        exact P.mul_mem_right _ h1
      · have hlt : n / Nat.gcd n m < n := Nat.div_lt_self hn hg1
        have hpos : 0 < n / Nat.gcd n m := Nat.div_pos (Nat.gcd_le_left m hn) hg0
        exact ih (n / Nat.gcd n m) hlt hpos h1

theorem isPrincipalIdealRing_loc {K : Type} [Field K] [NumberField K] (m : ℕ) (hm : 0 < m)
    (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 K) R]
    [IsLocalization (coprimeSet (𝓞 K) m) R] : IsPrincipalIdealRing R := by
  classical
  have hS := coprimeSet_le (𝓞 K) m
  have : IsDedekindDomain R := IsLocalization.isDedekindDomain (𝓞 K) hS R
  have hinj := IsLocalization.injective R hS
  have hm0 : (m : R) ≠ 0 := by
    rw [← map_natCast (algebraMap (𝓞 K) R), map_ne_zero_iff _ hinj]
    exact Nat.cast_ne_zero.mpr hm.ne'
  have hu : ∀ k : ℕ, 0 < k → k.Coprime m → IsUnit (k : R) := by
    intro k hk hc
    have := IsLocalization.map_units R (⟨(k : 𝓞 K), k, hk, hc, rfl⟩ : coprimeSet (𝓞 K) m)
    simpa using this
  refine IsPrincipalIdealRing.of_finite_primes ?_
  have hI : Ideal.span {(m : R)} ≠ 0 := by simpa using hm0
  refine (((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥).subset ?_
  intro P hP
  have hP : P.IsPrime := hP
  by_cases h0 : P = ⊥
  · exact Or.inl h0
  · refine Or.inr ⟨⟨P, hP, h0⟩, ?_, rfl⟩
    have h1 : P.under (𝓞 K) ≠ ⊥ := (IsLocalization.bot_lt_under_prime _ R hS P h0).ne'
    have h2 := Ideal.absNorm_mem (P.under (𝓞 K))
    have h3 : Ideal.absNorm (P.under (𝓞 K)) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    have h4 : ((Ideal.absNorm (P.under (𝓞 K)) : ℕ) : R) ∈ P := by
      rw [← map_natCast (algebraMap (𝓞 K) R)]
      exact h2
    have := mem_of_natCast_mem m hu P hP _ (Nat.pos_of_ne_zero h3) h4
    simpa [Ideal.dvd_iff_le] using this

theorem exists_basis_coprime {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m)
    (L : Submodule (𝓞 K) V) (hL : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  classical
  have hS := coprimeSet_le (𝓞 K) m
  set R := Localization.subalgebra K (coprimeSet (𝓞 K) m) hS with hR
  have : IsPrincipalIdealRing R := isPrincipalIdealRing_loc (K := K) m hm R
  have hst : IsScalarTower (𝓞 K) R V := ⟨fun a r v => by
    change ((a • (r : K)) • v) = a • ((r : K) • v)
    rw [smul_assoc]⟩

  have key : ∀ (M : Submodule (𝓞 K) V) (v : V), v ∈ Submodule.span R (M : Set V) →
      ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧ k • v ∈ M := by
    intro M v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simp, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨b, hb, hb', hy⟩ := hy
      refine ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩
      rw [smul_add]
      refine M.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact M.nsmul_mem hx b
      · rw [mul_smul]; exact M.nsmul_mem hy a
    | smul r x _ hx =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨⟨c, _, b, hb, hb', rfl⟩, hc⟩ := IsLocalization.surj (coprimeSet (𝓞 K) m) r
      refine ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩
      have h1 : (a * b) • r • x = c • (a • x) := by
        simp only [map_natCast] at hc
        rw [← algebraMap_smul R c, ← hc, mul_smul, smul_comm a, smul_comm a, mul_smul,
          Nat.cast_smul_eq_nsmul, smul_comm b r]
      rw [h1]
      exact M.smul_mem c hx
  let N : Submodule R V := Submodule.span R (L : Set V)
  have hN : N.FG := by
    obtain ⟨s, hs⟩ := hL
    refine ⟨s, ?_⟩
    simp only [N, ← hs]
    exact (Submodule.span_span_of_tower (𝓞 K) R (s : Set V)).symm
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  have : Module.IsTorsionFree R V := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r v h => ?_
    change (r : K) • v = 0 at h
    rcases smul_eq_zero.mp h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  obtain ⟨r, e⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := N)
  choose k hk hk' hkL using fun i => key L (e i : V) (e i).2
  refine ⟨r, fun i => k i • (e i : V), ?_, hkL, ?_⟩
  · have h1 : LinearIndependent R (fun i => (e i : V)) :=
      e.linearIndependent.map' N.subtype N.ker_subtype
    have h2 : LinearIndependent K (fun i => (e i : V)) :=
      (LinearIndependent.iff_fractionRing R K).mp h1
    have h3 := h2.units_smul (fun i => Units.mk0 (k i : K) (Nat.cast_ne_zero.mpr (hk i).ne'))
    convert h3 using 1
    funext i
    simp [Units.smul_def, Nat.cast_smul_eq_nsmul]
  · intro w hw
    have hwN : w ∈ N := Submodule.subset_span hw
    have h1 : w ∈ Submodule.span R
        ((Submodule.span (𝓞 K) (Set.range fun i => k i • (e i : V)) : Submodule (𝓞 K) V) : Set V) := by
      have h2 : w = ∑ i, e.repr ⟨w, hwN⟩ i • (e i : V) := by
        have := congrArg Subtype.val (e.sum_repr ⟨w, hwN⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      rw [h2]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      have hu : IsUnit (k i : R) := by
        have := IsLocalization.map_units R
          (⟨(k i : 𝓞 K), k i, hk i, hk' i, rfl⟩ : coprimeSet (𝓞 K) m)
        simpa using this
      obtain ⟨u, hu⟩ := hu
      have h3 : (e i : V) = ((u⁻¹ : Rˣ) : R) • (k i • (e i : V)) := by
        rw [← Nat.cast_smul_eq_nsmul R, ← hu, ← mul_smul, Units.inv_mul, one_smul]
      rw [h3]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
    obtain ⟨a, -, ha, h⟩ := key _ w h1
    exact ⟨a, ha, h⟩

end GlobalTheory.CoprimeBasisExistence
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLatticeBasisExists

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.HomLocBasis

open GlobalTheory.PlaceInt.LocBasis Module

theorem exists_basis_primeTo {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  first
  | exact @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | (apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime ..)


open Formalism.MainNotions.TaylorLogMetric in
theorem exists_nnBasis : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), p.Prime → Nat.Coprime (Ideal.absNorm cc) p → TaylorLogMetric.admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.NNBasis D (TaylorLogMetric.tor0 D cc δ) δ p L L' b := by
  intro D cc δ p N N' L L' hp hcc hA
  have hL : StandardLatticesGL3.SD D L := hA.2.2.1
  have hL' : StandardLatticesGL3.SD D L' := hA.2.2.2
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  let Y : Submodule (𝓞 D.host.K) (Matrix (Fin N') (Fin N) D.host.E) :=
    Submodule.span (𝓞 D.host.K) (Set.range y)
  have hYle : ∀ x ∈ Y, x ∈ YYl D L L' := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    exact (YYl D L L').sum_mem fun i _ => GlobalTheory.ThetaConj.smul_mem_YYl D L L' (c i) (hy i)
  have hYge : ∀ x ∈ YYl D L L', x ∈ Y := by
    intro x hx
    have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨t, ?_⟩
    conv_rhs => rw [hexp x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ht]; rfl
  obtain ⟨r, b, hli, hb, hw⟩ := exists_basis_primeTo p hp.pos Y (Submodule.fg_span (Set.finite_range y))
  set n : ℕ := Ideal.absNorm cc with hn
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, Nat.coprime_zero_left] at hcc
    exact hp.one_lt.ne' hcc
  have hnK : (n : D.host.K) ≠ 0 := by exact_mod_cast hn0
  refine ⟨r, fun i => n • b i, ⟨?_, fun i => ?_, fun w hwY => ?_⟩, fun i => ?_⟩
  · have := hli.units_smul fun _ => Units.mk0 _ hnK
    have e : (fun i => n • b i) = (fun _ : Fin r => Units.mk0 _ hnK) • b := by
      funext i
      simp [Units.smul_def, Nat.cast_smul_eq_nsmul]
    rw [e]; exact this
  · refine ⟨1, by simp, ?_⟩
    rw [Nat.cast_one, one_smul]
    exact nsmul_mem (hYle _ (hb i)) n
  · obtain ⟨k, hk, hkw⟩ := hw w (hYge w hwY)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hkw
    refine ⟨n * k, Nat.Coprime.mul_left hcc hk, c, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, mul_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]; rfl
  · refine AddSubgroup.subset_closure ⟨δ * n, AddSubgroup.subset_closure ⟨(n : 𝓞 D.host.K), Ideal.absNorm_mem cc, ?_⟩,
      b i, hYle _ (hb i), ?_⟩
    · simp
    · funext τ j k
      change δ * embT D τ ((n • b i) j k) = δ * n * embT D τ (b i j k)
      rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul, mul_assoc]

end GlobalTheory.HomLocBasis
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLatticeBasisExistsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.admissible_lattice_basis_exists : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), p.Prime → Nat.Coprime (Ideal.absNorm cc) p → TaylorLogMetric.admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.NNBasis D (TaylorLogMetric.tor0 D cc δ) δ p L L' b := by
  first | exact @GlobalTheory.HomLocBasis.exists_nnBasis | exact GlobalTheory.HomLocBasis.exists_nnBasis | (intros; apply GlobalTheory.HomLocBasis.exists_nnBasis <;> assumption)
end
end
