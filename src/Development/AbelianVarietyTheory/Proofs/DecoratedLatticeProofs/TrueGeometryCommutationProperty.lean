module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtKStdOfTwist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenomNotMemOfPrInt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadsRename
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimes
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FullOfSpanEqTop

section

@[expose] public section

namespace GlobalTheory.FullLatticeOfSpan

open NumberField

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (N : Submodule (𝓞 E) V) {x : V}
    (hx : x ∈ Submodule.span E (N : Set V)) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hay
    · rw [mul_smul]; exact N.smul_mem _ hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hsE : algebraMap (𝓞 E) E s ≠ 0 := by
      intro h
      exact hs0 (IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero]))
    refine ⟨a * s, mul_ne_zero ha hs0, ?_⟩
    have : (a * s) • ((algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s) • y) = r • (a • y) := by
      rw [← algebraMap_smul E (a * s), ← algebraMap_smul E r, ← algebraMap_smul E a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact N.smul_mem _ hay

theorem exists_nat_dvd {E : Type} [Field E] [NumberField E] (d : 𝓞 E) (hd : d ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ d ∣ (m : 𝓞 E) := by
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd
  · exact Ideal.mem_span_singleton.mp (Ideal.absNorm_mem _)

theorem full_of_span_eq_top : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (N : Submodule (NumberField.RingOfIntegers E) (Formalism.L2.Col.Sp E n)),
    Submodule.span E (↑N : Set (Formalism.L2.Col.Sp E n)) = ⊤ → GlobalTheory.ThetaMove.Full N := by
  intro E _ _ n N hN x
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem N (x := x) (by rw [hN]; trivial)
  obtain ⟨m, hm, c, hc⟩ := exists_nat_dvd d hd
  refine ⟨m, hm, ?_⟩
  rw [hc, mul_comm, mul_smul]
  exact N.smul_mem _ hdx

end GlobalTheory.FullLatticeOfSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiCpl1EqZeroOfFrames

section

@[expose] public section

open NumberField IsDedekindDomain Matrix ValuativeRel Formalism.L2.Col
open scoped Classical

noncomputable section

namespace GlobalTheory.CplDead

open Formalism.HermitianLatticesTheory GlobalTheory.ThetaMove

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem full_finset_inf {W ι : Type} [AddCommGroup W] [Module (𝓞 E) W] (S : Finset ι) (M : ι → Submodule (𝓞 E) W)
    (hM : ∀ i, Full (M i)) : Full (S.inf M) := by
  induction S using Finset.induction_on with
  | empty => intro x; exact ⟨1, one_pos, by simp⟩
  | insert i S hi ih => rw [Finset.inf_insert]; exact (hM i).inf ih

theorem exists_approx_family {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (M : HeightOneSpectrum (𝓞 E) → Submodule (𝓞 E) W) (hM : ∀ P, Full (M P)) (x : HeightOneSpectrum (𝓞 E) → W) :
    ∃ t : W, ∀ P ∈ S, t - x P ∈ localization₂ P.asIdeal (M P) := by
  have h := fun P => (full_finset_inf S M hM).approx {P} (x P)
  choose t h1 h2 using h
  refine ⟨∑ P ∈ S, t P, fun P hP => localization_mono P (Finset.inf_le hP) ?_⟩
  rw [← Finset.add_sum_erase S t hP, add_sub_right_comm]
  refine Submodule.add_mem _ (h1 P P (Finset.mem_singleton_self P)) (Submodule.sum_mem _ fun Q hQ => h2 Q P ?_)
  rw [Finset.mem_singleton]
  exact (Finset.ne_of_mem_erase hQ).symm

theorem full_of_span {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) (hN : Submodule.span E (N : Set (Sp E n)) = ⊤) : Full N := by
  first
  | exact @_root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top
  | exact _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top
  | (apply _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top ..)

theorem full_stdLat (n : ℕ) : Full (stdLat E n) := by
  refine full_of_span _ (top_le_iff.1 fun x _ => ?_)
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span fun j _ => ?_)
  by_cases h : i = j
  · simp only [if_pos h]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · simp only [if_neg h]; exact Submodule.zero_mem _

theorem intAt_of_mem_stdAt {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {x : Sp E n} (hx : x ∈ stdAt E n P) (i : Fin n) :
    IntAt P (x i) := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx i (Set.mem_univ i))
  exact ⟨r, s, hs, by rw [hr]; rfl⟩

variable {a b : ℕ}

def homInto (S₀ : Set (Sp E a)) (g : Sp E b →ₗ[E] Sp E b) (N : Submodule (𝓞 E) (Sp E b)) : Submodule (𝓞 E) (HomE E a b) where
  carrier := {z | ∀ y ∈ S₀, g (z y) ∈ N}
  zero_mem' := fun y _ => by simp
  add_mem' := fun {z z'} hz hz' y hy => by
    rw [LinearMap.add_apply, map_add (f := _)]; exact N.add_mem (hz y hy) (hz' y hy)
  smul_mem' := fun c z hz y hy => by
    rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower]; exact N.smul_mem _ (hz y hy)

theorem full_homInto (S₀ : Finset (Sp E a)) (g : Sp E b →ₗ[E] Sp E b) {N : Submodule (𝓞 E) (Sp E b)} (hN : Full N) :
    Full (homInto (S₀ : Set (Sp E a)) g N) := by
  intro z
  choose n hn hz using fun y => hN (g (z y))
  refine ⟨∏ y ∈ S₀, n y, Finset.prod_pos fun y _ => hn y, fun y hy => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower, ← Finset.prod_erase_mul S₀ n hy, Nat.cast_mul, mul_smul]
  exact N.smul_mem _ (hz y)

theorem apply_mem_of_mem_locP {S₀ : Set (Sp E a)} {g : Sp E b →ₗ[E] Sp E b} {N : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} {z : HomE E a b} (hz : z ∈ localization₂ P.asIdeal (homInto S₀ g N)) {y : Sp E a}
    (hy : y ∈ localization₂ P.asIdeal (Submodule.span (𝓞 E) S₀)) : g (z y) ∈ localization₂ P.asIdeal N := by
  obtain ⟨s, hs, hz⟩ := hz
  obtain ⟨t, ht, hy⟩ := hy
  have h : ∀ w ∈ Submodule.span (𝓞 E) S₀, g ((s • z) w) ∈ N := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact hz w hw
    | zero => simp
    | add u v _ _ hu hv => rw [map_add (f := _), map_add (f := _)]; exact N.add_mem hu hv
    | smul c u _ hu => rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]; exact N.smul_mem _ hu
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  have := h _ hy
  rwa [LinearMap.smul_apply, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
    smul_smul] at this

variable [StarRing E]

theorem phiT_add (K : Type) [Field K] {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG)
    {d' : Deco E b ST SG'} (hd' : d'.Ok) (x z : HomE E a b)
    (hz : ∀ P : ST, ∀ y ∈ d.at P.1, ((qOf P.1 : E))⁻¹ • z y ∈ d'.at P.1) : phiT K d d' (x + z) = phiT K d d' x := by
  have key : ∀ x z : HomE E a b, (∀ P : ST, ∀ y ∈ d.at P.1, ((qOf P.1 : E))⁻¹ • z y ∈ d'.at P.1) →
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) →
      ∀ P : ST, ∀ y ∈ d.at P.1, (x + z) y ∈ d'.at P.1 ∧ d'.f P ((x + z) y) = d.f P y := by
    intro x z hz hx P y hy
    have hq : (qOf P.1 : E) ≠ 0 := by
      have : qOf P.1 ≠ 0 := by rw [qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot
      exact_mod_cast this
    have e : z y = (qOf P.1 : 𝓞 E) • ((qOf P.1 : E))⁻¹ • z y := by
      rw [← algebraMap_smul E (qOf P.1 : 𝓞 E), map_natCast, smul_smul, mul_inv_cancel₀ hq, one_smul]
    have h1 : z y ∈ d'.at P.1 := by rw [e]; exact Submodule.smul_mem _ _ (hz P y hy)
    have h2 : d'.f P (z y) = 0 := by
      rw [e, hd'.f_smul P _ _ (hz P y hy), Ideal.Quotient.eq_zero_iff_mem.2
        (show (qOf P.1 : 𝓞 E) ∈ P.1.asIdeal from Ideal.absNorm_mem _), zero_mul]
    rw [LinearMap.add_apply]
    exact ⟨Submodule.add_mem _ (hx P y hy).1 h1, by rw [hd'.f_add P _ (hx P y hy).1 _ h1, h2, add_zero, (hx P y hy).2]⟩
  unfold phiT
  refine if_congr ⟨fun h => ?_, key x z hz⟩ rfl rfl
  have := key (x + z) (-z) (fun P y hy => by
    rw [LinearMap.neg_apply, smul_neg]; exact Submodule.neg_mem _ (hz P y hy)) h
  rwa [add_neg_cancel_right] at this

theorem exists_transport (K : Type) [Field K] {ST SG SG' SB : Finset (HeightOneSpectrum (𝓞 E))} (hdis : Disjoint ST SB)
    {d : Deco E a ST SG} (hd : d.Ok) {d' : Deco E b ST SG'} (hd' : d'.Ok) (f₀ : Frs E a SB) (f f' : Frs E b SB)
    (c : SB → E) (x : HomE E a b) :
    ∃ x' : HomE E a b, phiT K d d' x' = phiT K d d' x ∧
      ∀ (P : SB) s l, IntAt P.1 (c P * (inFr (f₀ P) (f P) x' - inFr (f₀ P) (f' P) x) (Pi.single s 1) l) := by
  obtain ⟨S₀, hS₀⟩ := hd.lat.fg
  obtain ⟨S₁, hS₁⟩ := hd'.lat.fg
  have hone : Full (1 : Submodule (𝓞 E) E) := by
    intro x
    obtain ⟨n, hn, hnx⟩ := full_stdLat (E := E) 1 (fun _ => x)
    refine ⟨n, hn, ?_⟩
    simpa [stdLat, Submodule.mem_pi] using hnx (0 : Fin 1) (Set.mem_univ _)
  have hfull : Full d'.N := by
    let M : Sp E b → Submodule (𝓞 E) (Sp E b) := fun y =>
      (1 : Submodule (𝓞 E) E).comap ((hStd E b y).restrictScalars (𝓞 E))
    have hM : ∀ y, Full (M y) := by
      intro y x
      obtain ⟨n, hn, hx⟩ := hone (hStd E b y x)
      refine ⟨n, hn, ?_⟩
      simpa [M] using hx
    have hle : S₁.inf M ≤ d'.N := by
      intro x hx
      rw [← hd'.uni]
      simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply]
      intro y hy
      rw [← hS₁] at hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact (show S₁.inf M ≤ M y from Finset.inf_le hy) hx
      | zero => simp
      | add y z hy hz ihy ihz => simpa using Submodule.add_mem (1 : Submodule (𝓞 E) E) ihy ihz
      | smul r y hy ih =>
        let r' : 𝓞 E := ⟨star (r : E), r.isIntegral_coe.map (starRingEnd E).toIntAlgHom⟩
        rw [← algebraMap_smul E r y, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
        have hr := (1 : Submodule (𝓞 E) E).smul_mem r' ih
        change star (r : E) * hStd E b y x ∈ (1 : Submodule (𝓞 E) E) at hr
        simpa [starRingEnd_apply, smul_eq_mul] using hr
    intro x
    obtain ⟨n, hn, hx⟩ := full_finset_inf S₁ M hM x
    exact ⟨n, hn, hle hx⟩
  obtain ⟨t, ht⟩ := exists_approx_family (W := HomE E a b) (ST ∪ SB)
    (fun P => if h : P ∈ SB then
        homInto ((Finset.univ.image fun s : Fin a => f₀ ⟨P, h⟩ (Pi.single s 1) : Finset (Sp E a)) : Set (Sp E a))
          (c ⟨P, h⟩ • (f ⟨P, h⟩).symm.toLinearMap) (stdLat E b)
      else homInto (S₀ : Set (Sp E a)) (((qOf P : E))⁻¹ • LinearMap.id) d'.N)
    (fun P => by
      by_cases h : P ∈ SB
      · simp only [dif_pos h]; exact full_homInto _ _ (full_stdLat b)
      · simp only [dif_neg h]; exact full_homInto _ _ hfull)
    (fun P => if h : P ∈ SB then (f ⟨P, h⟩).toLinearMap ∘ₗ (f' ⟨P, h⟩).symm.toLinearMap ∘ₗ x else x)
  refine ⟨t, ?_, fun P s l => ?_⟩
  · rw [← add_sub_cancel x t]
    refine phiT_add K d hd' x _ fun P y hy => ?_
    have h : P.1 ∉ SB := Finset.disjoint_left.1 hdis P.2
    have h1 := ht P.1 (Finset.mem_union_left _ P.2)
    simp only [dif_neg h] at h1
    exact apply_mem_of_mem_locP h1 (by rw [hS₀]; exact hy)
  · have h1 := ht P.1 (Finset.mem_union_right _ P.2)
    simp only [dif_pos P.2] at h1
    have h2 := apply_mem_of_mem_locP h1 (y := f₀ P (Pi.single s 1))
      (mem_localization_of_mem _ (Submodule.subset_span (by simp)))
    have h3 := intAt_of_mem_stdAt h2 l
    convert h3 using 1
    simp [inFr]

end Gen

theorem xiCpl1_eq_zero_of_frames : ∀ {X : Fields} {Pr : Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Formalism.L2.DIV.Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word), Disjoint (Pr.vT u) (rowSG Pr sel mu) → ∀ (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p p' : ChPt (R := R) sel mu u (m2 + 1)) (Y Y' : Set (Sp X.E (R.N (m2 + 1)))), p'.deco = p.deco → (∀ P : rowSG Pr sel mu, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • ((frsF sel mu p' P).symm (repY Y') - (frsF sel mu p P).symm (repY Y)) ∈ stdAt X.E (R.N (m2 + 1)) P.1) → (∀ x, XiCpl1 Ch sel mu cst L m2 al p₀ p Y x = 0) → ∀ x, XiCpl1 Ch sel mu cst L m2 al p₀ p' Y' x = 0 := by
  intro X Pr R Ch sel S mu cst L G m2 hL u hdis al p₀ p p' Y Y' hdeco hY h0 x
  obtain ⟨x', h1, h2⟩ := exists_transport X.K hdis p₀.deco.2 p.deco.2 (frsF sel mu p₀) (frsF sel mu p) (frsF sel mu p')
    (fun P => ((qOf P.1 : X.E) ^ cst.B)⁻¹) x
  rw [← h0 x']
  unfold XiCpl1
  rw [hdeco, h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have e1 := hL.psiInvX al P (inFr (frsF sel mu p₀ P) (frsF sel mu p' P) x) _ ((frsF sel mu p P).symm (repY Y)) (h2 P)
  have e2 := hL.psiInv al P (inFr (frsF sel mu p₀ P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))
    ((frsF sel mu p' P).symm (repY Y') - (frsF sel mu p P).symm (repY Y)) (fun i => intAt_of_mem_stdAt (hY P) i)
  rw [add_sub_cancel] at e1 e2
  rw [e1, e2]

end GlobalTheory.CplDead
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationProperty

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.Rebase
open ValuativeRel

theorem mem_grpAt_of_bc {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (P : GlobalTheory.FinPl.Pl D → Prop) (h : GA D V) (hh : h ∈ GfC V)
    (κ : GL (Fin n) (EF D)) (hκ : finM V hn h = κ.1)
    (hoff : ∀ v, ¬ P v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) κ = 1) : h ∈ GlobalTheory.FinPl.grpAt V P := by
  subst hn
  refine (GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts V P h).2 fun i j => ⟨(GlobalTheory.FinPl.SetCut.mem_GfC_iff_entries V h).1 hh i j, fun w hw => ?_⟩
  have e1 : Formalism.UG.prV (E := D.host.E) w (κ.1 i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun g => g.1 i j) (hoff w hw)
  rw [← hκ, GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply] at e1
  have e2 : Formalism.UG.prV (E := D.host.E) w (toEAf D ((Formalism.L2.Theta.mt V h - 1) i j)) = 0 := by
    rw [Matrix.sub_apply, RingHom.map_sub, map_sub, e1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e3 := (GlobalTheory.StabOff.prV_comm w (finPart D ((Formalism.L2.Theta.mt V h - 1) i j))).symm.trans e2
  exact (map_eq_zero_iff _ (Algebra.TensorProduct.comm _ _ _).injective).1 e3

theorem pr_mem_of_intAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt q.e P) {x : D.host.E}
    (hx : Formalism.L2.Col.IntAt P x) : q.pr (incA D x) ∈ 𝒪[k] := by
  obtain ⟨r, s, hs, e⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ P.asIdeal.zero_mem)
  have hsE : (s : D.host.E) ≠ 0 := fun h => hs0 (RingOfIntegers.coe_eq_zero_iff.mp h)
  have h1 := not_not.1 (mt (GlobalTheory.PhiOneVal.mem_prime_iff_pr_inv_notMem q P hP s hs0).2 hs)
  have e' : x = (r : D.host.E) * (s : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hsE, mul_comm]
    exact e
  rw [e', map_mul, map_mul]
  exact mul_mem (GlobalTheory.LocMod.FullLatFrame.pr_int_mem q r) h1

theorem map_pr_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt q.e P)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (h : GA D V) (r : (Fin n → D.host.E) →ₗ[D.host.E] (Fin n → D.host.E))
    (hr : ∀ i j, adAt D.host.F P (finM V hn h i j) = algebraMap D.host.E _ (r (Pi.single j 1) i))
    {Y : Type} [Fintype Y] [DecidableEq Y] (pos : Y → ℕ) (F : GlobalTheory.LocMod.Frame k V.rank Y) (hF : IsStdFr pos F) (e : Y ≃ Fin n)
    (he : GlobalTheory.SymBridge.IsOrd pos e) :
    (Formalism.L2.Theta.mt V h).map q.pr = F.β * GlobalTheory.SymBridge.toLoc (q.pr.comp (incA D)) e e r * F.γ := by
  subst hn
  obtain ⟨e', he', hF⟩ := hF
  obtain rfl : e = e' := Equiv.ext fun y => Fin.ext ((he y).trans (he' y).symm)
  refine Matrix.ext fun c d => ?_
  obtain ⟨c, rfl⟩ := e.surjective c
  obtain ⟨d, rfl⟩ := e.surjective d
  rw [GlobalTheory.Fam.MovedJoin.mul_frameγ_std _ e hF, GlobalTheory.Fam.MovedJoin.frameβ_mul_std _ e hF]
  have h1 := hr (e c) (e d)
  rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply] at h1
  exact GlobalTheory.SplitProj.pr_eq_of_adAt q P hP _ _ h1

theorem toHom_surj {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) :
    Function.Surjective (toHom S T hS hT) := fun x =>
  ⟨(Matrix.reindex (finCongr hT) (finCongr hS)).symm (LinearMap.toMatrix' x), by
    unfold toHom
    rw [Equiv.apply_symm_apply, Matrix.toLin'_toMatrix']⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

open Formalism.L2.Col GlobalTheory.StepData GlobalTheory.SymBridge

theorem disjoint_vT (hI : I.Ok) (u : B.Word) (b : I.ι) : Disjoint ((B.primes X).vT u) (rowSG (B.primes X) I.sel (I.tup b)) := by
  refine Finset.disjoint_left.2 fun P h1 h2 => ?_
  obtain ⟨hX, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have h3 := (GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup b) u hX hPr hI.sel_ok
    (hI.T_mem u) hI.g_mem P (Finset.mem_union_left _ h1)).2.2.2.2 h1
  refine GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P ?_ ?_
  · rcases Finset.mem_union.1 h2 with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (I.Q_subset_SQ b h)
  · show algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.asIdeal
    rw [map_natCast]
    exact h3








theorem dead_moved (hI : I.Ok) {b : I.ι} {Ch₀ Ch : ℕ → Type} {A A' : TwDat I l Z u b Ch₀} {ι : ∀ j, Ch j → Ch₀ j} (hl : A.Live ι)
    (hb : A'.b0 = A.b0) (hne : ∀ i, i + 1 ≠ B.R.m → A'.p0 i = A.p0 i)
    (heq : ∀ i, i + 1 = B.R.m → ∀ β, (A'.p0 i β).1.1.deco = (A.p0 i β).1.1.deco ∧ cosetIn (A'.p0 i β) = cosetIn (A.p0 i β)) :
    A'.Live ι := by
  refine ⟨hl.inj, hl.first, hl.last, fun j hj γ hγ α z => ?_⟩
  by_cases h1 : j + 1 = B.R.m
  · refine absurd ?_ hγ
    have : ∀ k, k = B.R.m → Function.Surjective (ι k) := by
      rintro _ rfl
      exact hl.last
    exact this _ h1 γ
  by_cases h2 : j + 2 = B.R.m
  swap
  · have h := hl.dead j hj γ hγ α z
    unfold TwDat.xi at h ⊢
    rw [hb, hne j h1, hne (j + 1) h2]
    exact h
  have hL : (I.idx b).Ok I.Ch I.sel (I.tup b) (I.cst b) I.glob j := by
    have := hI.idx_ok b
    rwa [show B.R.m - 2 = j by omega] at this
  obtain ⟨hd, hc⟩ := heq (j + 1) h2 γ
  have key := GlobalTheory.CplDead.xiCpl1_eq_zero_of_frames I.Ch I.sel (I.tup b) (I.cst b) (I.idx b) I.glob j hL u (disjoint_vT hI u b)
    ((A.b0 j α).get (by omega)) (A.p0 j α).1.1 (A.p0 (j + 1) γ).1.1 (A'.p0 (j + 1) γ).1.1 (A.p0 (j + 1) γ).1.2 (A'.p0 (j + 1) γ).1.2 hd
    (GlobalTheory.AdForm.Rebase.repY_cong h2 _ _ hc) (fun x => ?_)
  · unfold TwDat.xi
    rw [hb, hne j h1]
    unfold xiAt
    rw [dif_neg (by omega), dite_eq_left h2]
    exact (congrArg B.embLL (key _)).trans (map_zero _)
  · obtain ⟨z', hz'⟩ := toHom_surj _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) x
    have h := hl.dead j hj γ hγ α z'
    unfold TwDat.xi xiAt at h
    rw [dif_neg (by omega), dite_eq_left h2] at h
    subst hz'
    exact (map_eq_zero_iff _ B.embLL.injective).1 h


end GlobalTheory.Fam.Rebase

namespace GlobalTheory.Fam
open GlobalTheory.Fam.Rebase


end GlobalTheory.Fam

end
end
end
