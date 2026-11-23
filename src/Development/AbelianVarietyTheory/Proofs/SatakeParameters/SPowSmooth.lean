module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckePowOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
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
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HarrisTaylorOrderSplitAlmostAllPrimesStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothOfRelativeDimensionFibrePower

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BilinFormInjectiveExistsNsmulMemRange

section

@[expose] public section

namespace GlobalTheory

open Matrix

theorem bilinForm_injective_exists_mul_mem_range (La : Type) [AddCommGroup La]
    [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La)
    (hEF : Function.Injective EF) :
    ∃ e : ℕ, 0 < e ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f := by
  classical
  set ι := Module.Free.ChooseBasisIndex ℤ La
  let b : Module.Basis ι ℤ La := Module.Free.chooseBasis ℤ La
  let A : Matrix ι ι ℤ := fun i j => EF (b i) (b j)

  have key : ∀ (c : ι → ℤ) (j : ι), EF (∑ i, c i • b i) (b j) = (c ᵥ* A) j := by
    intro c j

    simp [map_sum, map_smul, LinearMap.sum_apply, vecMul, dotProduct, A, smul_eq_mul]
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvA⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := A)).2 h0
    have hx : EF (∑ i, v i • b i) = 0 := by
      refine b.ext fun j => ?_
      rw [key, hvA]; simp
    have : (∑ i, v i • b i) = 0 := hEF (by rw [hx, map_zero])
    apply hv
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent v this i
  set d := A.det
  refine ⟨d.natAbs * d.natAbs, ?_, ?_⟩
  · have : 0 < d.natAbs := Int.natAbs_pos.2 hdet
    positivity
  · intro f
    let w : ι → ℤ := fun j => f (b j)
    refine ⟨∑ i, ((d • w) ᵥ* adjugate A) i • b i, ?_⟩
    refine b.ext fun j => ?_
    rw [key, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]
    have hc : ((d.natAbs * d.natAbs : ℕ) : ℤ) = d * d := by
      rw [Nat.cast_mul]; exact Int.natAbs_mul_self' d
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, w]
    rw [← Nat.cast_smul_eq_nsmul ℤ, hc, smul_eq_mul]
    ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BilinFormInjectiveExistsNsmulMemRangeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.bilinForm_injective_exists_nsmul_mem_range : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La), Function.Injective EF → ∃ e : ℕ, 0 < e ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f := by
  first | (exact @GlobalTheory.bilinForm_injective_exists_mul_mem_range) | (exact GlobalTheory.bilinForm_injective_exists_mul_mem_range) | (intros; apply GlobalTheory.bilinForm_injective_exists_mul_mem_range  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHarrisTaylorDatumAtPrimeCoprime

section

@[expose] public section

open NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct

namespace GlobalTheory.GoodPrime

theorem schur (tr nm : ℤ) (M : ℕ) (hM : 0 < M) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M ∧ ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - tr * r + nm := by
  by_cases hnm : nm = 0
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := M + 1) (by omega)
    refine ⟨p, hp, fun h => hp.one_lt.ne' ?_, 0, by simp [hnm]⟩
    exact Nat.dvd_one.1 ((Nat.dvd_add_right h).1 hpd)
  · set t : ℤ := |tr| + 3
    set g : ℤ := (M : ℤ) ^ 2 * nm * t ^ 2 - tr * M * t + 1
    have ht : 3 ≤ t := by have := abs_nonneg tr; omega
    have hMz : (1 : ℤ) ≤ M := by exact_mod_cast hM
    have hnm1 : 1 ≤ |nm| := Int.one_le_abs hnm
    have hg : 2 ≤ |g| := by
      have h1 : |(M : ℤ) ^ 2 * nm * t ^ 2| = (M : ℤ) ^ 2 * |nm| * t ^ 2 := by
        rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos (by omega : (0:ℤ) < M), abs_of_pos (by omega : (0:ℤ) < t)]
      have h2 : |tr * M * t| = |tr| * M * t := by
        rw [abs_mul, abs_mul, abs_of_pos (by omega : (0:ℤ) < M), abs_of_pos (by omega : (0:ℤ) < t)]
      have h3 : |(M : ℤ) ^ 2 * nm * t ^ 2| ≤ |g| + |tr * M * t| + 1 := by
        have : (M : ℤ) ^ 2 * nm * t ^ 2 = g + tr * M * t - 1 := by simp only [g]; ring
        rw [this]
        calc |g + tr * M * t - 1| ≤ |g + tr * M * t| + |(1:ℤ)| := abs_sub _ _
          _ ≤ |g| + |tr * M * t| + 1 := by simpa using abs_add_le g (tr * M * t)
      rw [h1, h2] at h3
      have hat : |tr| = t - 3 := by simp only [t]; ring
      rw [hat] at h3
      have hMt : 3 ≤ (M : ℤ) * t := by nlinarith
      have hk : (M : ℤ) ^ 2 * t ^ 2 ≤ (M : ℤ) ^ 2 * |nm| * t ^ 2 := by
        have := mul_le_mul_of_nonneg_right hnm1 (by positivity : (0:ℤ) ≤ (M : ℤ) ^ 2 * t ^ 2)
        linarith
      have hq : 3 ≤ t * ((M : ℤ) - 1) + 3 := by nlinarith
      have hr : 9 ≤ ((M : ℤ) * t) * (t * ((M : ℤ) - 1) + 3) := by nlinarith
      have e : ((M : ℤ) * t) * (t * ((M : ℤ) - 1) + 3) = (M : ℤ) ^ 2 * t ^ 2 - (t - 3) * M * t := by ring
      linarith
    have hg' : (2 : ℤ) ≤ (g.natAbs : ℤ) := by rw [← Int.abs_eq_natAbs]; exact hg
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := g.natAbs) (by omega)
    have hpg : (p : ℤ) ∣ g := Int.natCast_dvd.2 hpd
    refine ⟨p, hp, fun h => hp.one_lt.ne' ?_, M * nm * t, ?_⟩
    · have hpM : (p : ℤ) ∣ M := Int.natCast_dvd_natCast.2 h
      have : (p : ℤ) ∣ g - M * (M * nm * t ^ 2 - tr * t) := dvd_sub hpg (dvd_mul_of_dvd_left hpM _)
      have e : g - M * (M * nm * t ^ 2 - tr * t) = 1 := by simp only [g]; ring
      rw [e] at this
      exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this
    · have e : ((M : ℤ) * nm * t) ^ 2 - tr * (M * nm * t) + nm = nm * g := by simp only [g]; ring
      rw [e]; exact dvd_mul_of_dvd_right hpg _

theorem exists_datum (G : GDatum) (N : ℕ) (hN : 0 < N) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (D : Datum p), N.Coprime p ∧ D.toG = G := by
  haveI := G.freeLa; haveI := G.finLa
  obtain ⟨e, he, hperf⟩ := GlobalTheory.T.bilinForm_injective_exists_nsmul_mem_range G.La G.EF G.nondeg
  obtain ⟨M, hM, hsplit⟩ := GlobalTheory.T.harrisTaylorOrder_split_almost_all_primes G
  have hd : 0 < (G.tr ^ 2 - 4 * G.nm).natAbs := Int.natAbs_pos.2 (ne_of_lt G.disc_neg)
  obtain ⟨p, hp, hpM, r, hr⟩ := schur G.tr G.nm (N * e * M * (G.tr ^ 2 - 4 * G.nm).natAbs) (by positivity)
  haveI : Fact p.Prime := ⟨hp⟩
  have hN' : ¬ p ∣ N := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _) _)
  have he' : ¬ p ∣ e := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _) _)
  have hM' : ¬ p ∣ M := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have hd' : ¬ (p : ℤ) ∣ G.tr ^ 2 - 4 * G.nm := fun h => hpM (Dvd.dvd.mul_left (Int.natCast_dvd.1 h) _)
  refine ⟨p, inferInstance,
    { F := G.F, fld := G.fld, nf := G.nf, cm := G.cm, bar := G.bar, bar_eq := G.bar_eq, ω := G.ω,
      tr := G.tr, nm := G.nm, tr_eq := G.tr_eq, nm_eq := G.nm_eq, disc_neg := G.disc_neg, disc_p := hd',
      split := ⟨r, hr⟩, O := G.O, rng := G.rng, alg := G.alg, freeO := G.freeO, finO := G.finO,
      m := G.m, m_pos := G.m_pos, rankO := G.rankO, central := G.central, star := G.star,
      star_star := G.star_star, star_F := G.star_F, splitP := hsplit p hM', La := G.La, acg := G.acg,
      modO := G.modO, freeLa := G.freeLa, finLa := G.finLa, n := G.n, n_pos := G.n_pos, rankLa := G.rankLa,
      EF := G.EF, alt := G.alt, nondeg := G.nondeg,
      perfP := ⟨e, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 he'), hperf⟩,
      adj := G.adj, a := G.a, ρc := G.ρc, ρc_root := G.ρc_root, tau := G.tau, tau_ω := G.tau_ω,
      dom := G.dom },
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hN'), rfl⟩

end GlobalTheory.GoodPrime
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHarrisTaylorDatumAtPrimeCoprimeStatement

section

@[expose] public section

open NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

theorem _root_.GlobalTheory.T.exists_harrisTaylorDatum_at_prime_coprime : ∀ (G : GDatum) (N : ℕ), 0 < N → ∃ (p : ℕ) (_ : Fact p.Prime) (D : Datum p), N.Coprime p ∧ D.toG = G := by
  first | (exact @GlobalTheory.GoodPrime.exists_datum) | (exact GlobalTheory.GoodPrime.exists_datum) | (intros; apply GlobalTheory.GoodPrime.exists_datum  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericModelComplexSmooth

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPel.HT.Gen.CxSmooth

theorem of_geomFibres {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (g : ℕ)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Y), SmoothOfRelativeDimension g (pullback.snd f t)) :
    SmoothOfRelativeDimension g f := by
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim f
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  have key : ∀ x, n x = g := by
    intro x
    let κ := Y.residueField (f x)
    let k := AlgebraicClosure κ
    let t : Sp k ⟶ Y := spMap (algebraMap κ k) ≫ Y.fromSpecResidueField (f x)
    have ht : f x = t (IsLocalRing.closedPoint k) := by
      show f x = (Y.fromSpecResidueField (f x)) ((spMap (algebraMap κ k)) (IsLocalRing.closedPoint k))
      rw [Scheme.fromSpecResidueField_apply]
    obtain ⟨z, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := t) x (IsLocalRing.closedPoint k) ht
    have sq := IsPullback.paste_vert (isPullback_morphismRestrict (pullback.fst f t) (W x))
      (IsPullback.of_hasPullback f t)
    have h₁ : SmoothOfRelativeDimension (n x) (((pullback.fst f t) ⁻¹ᵁ W x).ι ≫ pullback.snd f t) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback sq (hd x)
    have h₂ : SmoothOfRelativeDimension g (((pullback.fst f t) ⁻¹ᵁ W x).ι ≫ pullback.snd f t) :=
      IsZariskiLocalAtSource.comp (h k t) _
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h₁ h₂ ⟨z, show pullback.fst f t z ∈ W x by rw [hz.1]; exact hW x⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← key x]; exact hd x

def baseOfG {p : ℕ} [Fact p.Prime] {D : Datum p} (gb : GBase D.toG ℂ) : Base D ℂ where
  unit k hk := by
    refine Ne.isUnit (Nat.cast_ne_zero.2 ?_)
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hk)
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart i j _ k _ _ β := by
    exfalso
    have h1 : IsUnit ((p : ℂ)) := Ne.isUnit (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    have h2 := h1.map β
    rw [map_natCast, CharP.cast_eq_zero] at h2
    exact not_isUnit_zero h2

theorem genericModel_complex_smooth {p : ℕ} [Fact p.Prime] (D : Datum p) (gb : GBase D.toG ℂ) (N : ℕ) (hN : 3 ≤ N)
    (hNp : N.Coprime p) (X : GenModel gb N) : ∃ d, SmoothOfRelativeDimension d X.s := by
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D ℂ (baseOfG gb) N hN hNp
  obtain ⟨j, hj, -, hjs, -⟩ := GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre p D ℂ (baseOfG gb) ℂ (RingHom.id ℂ) gb rfl
    (fun i => (RingHom.id_comp _).symm) N hN hNp M X
  have h1 : SmoothOfRelativeDimension (D.a * (D.n - 1)) (pullback.snd M.s (spMap (RingHom.id ℂ))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) M.smooth
  have : IsOpenImmersion j := hj
  have h0 : SmoothOfRelativeDimension 0 j := inferInstance
  refine ⟨0 + D.a * (D.n - 1), ?_⟩
  rw [← hjs]
  infer_instance

theorem card_torsion_of_gTateIso (G : GDatum) {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    Nat.card {q : Q // q ^ ℓ = 1} = ℓ ^ Module.finrank ℤ G.La := by
  haveI := G.freeLa
  haveI := G.finLa
  haveI : NeZero ℓ := ⟨hℓ.ne'⟩
  set r := Module.finrank ℤ G.La
  let B := Module.finBasis ℤ G.La
  let v : (Fin r → ZMod ℓ) → G.La := fun c => ∑ i, ((c i).val : ℤ) • B i
  have evneg : ∀ x y : G.La, I.ev ℓ (x - y) = I.ev ℓ x * (I.ev ℓ y)⁻¹ := fun x y => by
    rw [eq_mul_inv_iff_mul_eq, ← I.add, sub_add_cancel]
  have hrep : ∀ c i, B.repr (v c) i = ((c i).val : ℤ) := fun c i => by
    simp [v, Module.Basis.repr_self, Finsupp.single_apply]
  let F : (Fin r → ZMod ℓ) → {q : Q // q ^ ℓ = 1} := fun c => ⟨I.ev ℓ (v c), (I.onto ℓ hℓ _).2 ⟨_, rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro c c' hcc
      have h1 : I.ev ℓ (v c - v c') = 1 := by
        rw [evneg, mul_inv_eq_one]; exact congrArg Subtype.val hcc
      obtain ⟨y, hy⟩ := (I.ker ℓ hℓ _).1 h1
      funext i
      have h2 := congrArg (fun z => B.repr z i) hy
      simp only [map_sub, Finsupp.sub_apply, hrep, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at h2
      have h3 := congrArg (fun z : ℤ => (z : ZMod ℓ)) h2
      simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_mul,
        ZMod.natCast_self, zero_mul] at h3
      exact sub_eq_zero.1 h3
    · rintro ⟨q, hq⟩
      obtain ⟨x, rfl⟩ := (I.onto ℓ hℓ q).1 hq
      let c : Fin r → ZMod ℓ := fun i => (B.repr x i : ZMod ℓ)
      have hdiv : ∀ i, (ℓ : ℤ) ∣ ((c i).val : ℤ) - B.repr x i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        simp [c]
      choose y hy using hdiv
      refine ⟨c, Subtype.ext ?_⟩
      show I.ev ℓ (v c) = I.ev ℓ x
      have e1 : v c = x + ℓ • ∑ i, y i • B i := by
        refine B.ext_elem fun i => ?_

        rw [hrep, map_add (f := _), map_nsmul, Finsupp.add_apply, Finsupp.smul_apply, map_sum]
        simp only [map_zsmul, Module.Basis.repr_self, Finset.sum_apply', Finsupp.smul_apply,
          Finsupp.single_apply, smul_eq_mul, nsmul_eq_mul]
        simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linear_combination hy i
      rw [e1, I.add, (I.ker ℓ hℓ _).2 ⟨_, rfl⟩, _root_.mul_one]
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem relDim_A {G : GDatum} (gb : GBase G ℂ) (N : ℕ) (X : GenModel gb N) :
    SmoothOfRelativeDimension (G.m * G.n * Module.finrank ℚ G.F / 2) X.univ.A.hom := by
  have hab := X.univ.ab
  have : Smooth X.univ.A.hom := hab.smooth
  have : IsProper X.univ.A.hom := hab.proper
  have : GeometricallyConnected X.univ.A.hom := hab.geomConnected
  refine of_geomFibres X.univ.A.hom _ fun k _ _ t => ?_
  let B := (Over.pullback t).obj X.univ.A
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := by show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have : Smooth B.hom := hB.smooth
  have : GeometricallyConnected B.hom := hB.geomConnected
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton (f := B.hom)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected B.hom (Classical.arbitrary _)
  suffices e : d = G.m * G.n * Module.finrank ℚ G.F / 2 by rw [← e]; exact hd
  obtain ⟨β, hβ⟩ := Spec.map_surjective (t ≫ X.s)
  obtain ⟨I, -⟩ := X.univ.geom k t β.hom hβ.symm
  have h2k : ((2 : ℕ) : k) ≠ 0 := by
    have h : IsUnit ((2 : ℕ) : ℂ) := Ne.isUnit (by norm_num)
    have := h.map β.hom
    rw [map_natCast] at this
    exact this.ne_zero
  have c₁ := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B d 2 hB hd h2k
  have c₂ := card_torsion_of_gTateIso G I (ℓ := 2) two_pos
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback X.univ.A t) (𝟙 _) t
    (Category.id_comp t).symm
  have c₃ : Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ 2 = 1} =
      Nat.card {q : Over.mk t ⟶ X.univ.A // q ^ 2 = 1} :=
    Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
      show x ^ 2 = 1 ↔ e x ^ 2 = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  rw [c₁, c₂, G.rankLa] at c₃
  have := Nat.pow_right_injective le_rfl c₃
  omega

theorem genModel_smooth : ∀ (G : GDatum) (gb : GBase G ℂ) (N : ℕ), 3 ≤ N → ∀ X : GenModel gb N,
    (∃ d : ℕ, SmoothOfRelativeDimension d X.s) ∧
      SmoothOfRelativeDimension (G.m * G.n * Module.finrank ℚ G.F / 2) X.univ.A.hom := by
  intro G gb N hN X
  refine ⟨?_, relDim_A gb N X⟩
  obtain ⟨p, _, D, hNp, rfl⟩ := GlobalTheory.T.exists_harrisTaylorDatum_at_prime_coprime G N (by omega)
  exact genericModel_complex_smooth D gb N hN hNp X

end GlobalTheory.UPel.HT.Gen.CxSmooth
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SPowSmooth

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.WeightTwoHeckePower

namespace GlobalTheory.WeightTwoHeckePower

theorem sPow_smooth : ∀ (G : GDatum) (gb : GBase G ℂ) (N : ℕ), 3 ≤ N → ∀ (X : GenModel gb N) (r : ℕ),
    ∃ d : ℕ, SmoothOfRelativeDimension d (sPow X r) := by
  intro G gb N hN X r
  obtain ⟨⟨d, hd⟩, hA⟩ := GlobalTheory.UPel.HT.Gen.CxSmooth.genModel_smooth G gb N hN X
  have h := GlobalTheory.FibPow.smoothOfRelativeDimension_pow X.univ.A _ hA r
  exact ⟨_, (inferInstance : SmoothOfRelativeDimension (r * (G.m * G.n * Module.finrank ℚ G.F / 2) + d)
    ((GlobalTheory.KS.pow X.univ.A r).hom ≫ X.s))⟩

end GlobalTheory.WeightTwoHeckePower
end
end
