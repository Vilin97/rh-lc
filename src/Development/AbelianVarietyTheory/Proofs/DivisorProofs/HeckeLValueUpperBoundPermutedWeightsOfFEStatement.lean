module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCompletedHeckeLCMOneLePhragmenLindelofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeLFunctionLeZetaThreeHalvesPowStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmValueCharacterConductorExponents

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.SqNum.CondExps

theorem exists_condExps : ∀ (D : D7) [IsCMField D.host.E] {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (s : ℕ)
    (κ : D.what₂.Tau → ℕ) (χ : HChar D.host.E), IsValChar (cmPhi D) s κ (condF G.pl) ∅ χ →
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) →₀ ℕ, (∀ v, ExpAt χ v (a v)) ∧
      (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) ≤ levQ G.pl ^ 2 := by
  intro D _ T Lc sc G s κ χ hχ
  let 𝔣 : Ideal (𝓞 D.host.F) := condF G.pl
  let 𝔐 : Ideal (𝓞 D.host.E) := 𝔣.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
  have hrank : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 :=
    (IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E).symm.trans
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
  have hnorm𝔣 : Ideal.absNorm 𝔣 = levQ G.pl := by
    simp only [𝔣, condF, levQ, map_prod, map_pow]
  have hlev : 0 < levQ G.pl := Finset.prod_pos fun v _ =>
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
  have hnorm𝔐 : Ideal.absNorm 𝔐 = levQ G.pl ^ 2 := by
    rw [Ideal.absNorm_algebraMap, hrank, hnorm𝔣]
  have h𝔐0 : 𝔐 ≠ ⊥ := fun h => by
    have h' := hnorm𝔐
    rw [h, Ideal.absNorm_bot] at h'
    exact (pow_pos hlev 2).ne' h'.symm
  let f : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun P => expIn (condF G.pl) (P.under (𝓞 D.host.F))
  have hdvd : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal ^ f P ∣ 𝔐 := fun P => by
    have h1 : (P.under (𝓞 D.host.F)).asIdeal ^ f P ∣ 𝔣 := pow_multiplicity_dvd _ _
    have h2 : P.asIdeal ∣ (P.under (𝓞 D.host.F)).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) :=
      Ideal.dvd_iff_le.2 Ideal.map_comap_le
    obtain ⟨c, hc⟩ := h1
    calc P.asIdeal ^ f P ∣ ((P.under (𝓞 D.host.F)).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) ^ f P :=
          pow_dvd_pow_of_dvd h2 _
      _ ∣ 𝔐 := by
          refine ⟨c.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), ?_⟩
          show 𝔣.map _ = _
          rw [hc, Ideal.map_mul, Ideal.map_pow]
  have hfin : (Function.support f).Finite := by
    refine (Ideal.finite_factors h𝔐0).subset fun P hP => ?_
    exact (dvd_pow_self _ hP).trans (hdvd P)
  refine ⟨Finsupp.ofSupportFinite f hfin, fun P => ?_, ?_⟩
  · exact (hχ.2.2.2 (P.under (𝓞 D.host.F)) P rfl).2 (Finset.notMem_empty _)
  · set a := Finsupp.ofSupportFinite f hfin
    have hJ : (a.prod fun P k => P.asIdeal ^ k) ∣ 𝔐 := by
      refine Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ => ?_) fun P _ => ?_
      · exact (Ideal.isCoprime_of_isMaximal fun h => hPQ (HeightOneSpectrum.ext h)).pow
      · exact hdvd P
    have e : (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) = Ideal.absNorm (a.prod fun P k => P.asIdeal ^ k) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [e, ← hnorm𝔐]
    exact Nat.le_of_dvd (hnorm𝔐 ▸ pow_pos hlev 2) (map_dvd Ideal.absNorm hJ)

end GlobalTheory.FunObj.SqNum.CondExps
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmValueCharacterConductorExponentsStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

theorem _root_.GlobalTheory.T.exists_cmValueCharacter_conductorExponents : ∀ (D : D7) [IsCMField D.host.E] {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (s : ℕ)
    (κ : D.what₂.Tau → ℕ) (χ : HChar D.host.E), IsValChar (cmPhi D) s κ (condF G.pl) ∅ χ →
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) →₀ ℕ, (∀ v, ExpAt χ v (a v)) ∧
      (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) ≤ levQ G.pl ^ 2 := by
  first | exact @GlobalTheory.FunObj.SqNum.CondExps.exists_condExps | exact GlobalTheory.FunObj.SqNum.CondExps.exists_condExps | (intros; apply GlobalTheory.FunObj.SqNum.CondExps.exists_condExps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSizesLogBound

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.SqTop GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid

namespace GlobalTheory.SqTop.SizesBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T}

theorem auxiliaryProduct_mem_place_of_exceptionalSet (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    ((D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have hp := v.isPrime
  simp only [Nat.cast_mul, hp.mul_mem_iff_mem_or_mem]
  rcases P.mem_S0_of_sum_eq.1 hv with rfl | h
  · exact Or.inr P.basePlace_over_qZero
  · rcases (S1_mem_OmF D).1 h with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)

theorem levQ_le (P : Places L) :
    levQ P ≤ ((D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D) ^ Module.finrank ℤ (𝓞 D.host.F)) ^ 2 := by
  classical
  set M := D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D with hM
  have hmem : ((M : ℕ) : 𝓞 D.host.F) ∈ ∏ v ∈ P.S0, v.asIdeal := by
    rw [← Ideal.dvd_span_singleton]
    exact Finset.prod_dvd_of_coprime (fun v _ w _ hne => HeightOneSpectrum.isCoprime_of_ne v w hne)
      fun v hv => Ideal.dvd_span_singleton.2 (auxiliaryProduct_mem_place_of_exceptionalSet P hv)
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  rw [Ideal.absNorm_span_natCast, map_prod] at hdvd
  have hM0 : 0 < M := by
    have := (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
    have := (D.host.g_prime 0).pos
    have := (D.host.g_prime 1).pos
    have := D.host.pde_prime.pos
    have := D.host.pde'_prime.pos
    positivity
  have hle := Nat.le_of_dvd (pow_pos hM0 _) hdvd
  calc levQ P = ∏ v ∈ P.S0, Ideal.absNorm v.asIdeal ^ condExp P v := rfl
    _ ≤ ∏ v ∈ P.S0, Ideal.absNorm v.asIdeal ^ 2 := by
      refine Finset.prod_le_prod' fun v _ => Nat.pow_le_pow_right ?_ ?_
      · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
      · unfold condExp; split_ifs <;> norm_num
    _ = (∏ v ∈ P.S0, Ideal.absNorm v.asIdeal) ^ 2 := Finset.prod_pow _ _ _
    _ ≤ _ := Nat.pow_le_pow_left hle 2

theorem kap_add_le (large₂ : SizeData₂ D) (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (i j : Fin D.R.m) {s : ℕ}
    (hs : s ≤ halfRank D i j) (τ : D.what₂.Tau) : (kap D 1 i j s τ : ℝ) + s ≤ 5 * large₂.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSc, hhc, -⟩ := h
  have e := (Model.kap_add D 1 i j τ hs).1
  have e' := congrArg (Int.cast : ℤ → ℝ) e
  push_cast at e'
  rw [e']

  have he : (((num D 1 τ).e (j + 1) : ℤ) : ℝ) ≤ 4 * large₂.sc.b := by
    have s1 := ((GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).2.2 j)
    have s2 : (((D.hc τ).e j : ℚ) : ℝ) = (((num D 1 τ).e (j + 1) : ℤ) : ℝ) := by
      rw [s1]; push_cast; rfl
    rw [← s2]; exact (hhc τ j).2

  set G0 := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG0
  have hk := D.R.m_add_three_le_k
  have hv0 : 0 < D.R.k - 1 := by omega
  have hv : (G0.v 2 : ℚ) ≤ large₂.Sc := by
    have s1 := (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) 0).1 ⟨0, hv0⟩
    have := (large₂.cloud_v τ ⟨0, hv0⟩).2
    rw [s1] at this
    exact_mod_cast this
  have hmid : ((G0.mid (D.R.m - i) : ℚ) : ℝ) ≤ large₂.Sc + ((D.R.m : ℝ) + 1) * gap D 1 + 1 / 2 := by
    have hi := i.2
    have hm : G0.m = D.R.m := rfl
    have hg : G0.ga = gap D 1 := rfl
    simp only [GlobalTheory.SignedHC.GridData.mid, GlobalTheory.SignedHC.GridData.a, hm, hg]
    have hg0 : (0 : ℝ) ≤ gap D 1 := by positivity
    have hi' : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast hi
    have hv' : ((G0.v 2 : ℚ) : ℝ) ≤ large₂.Sc := by exact_mod_cast hv
    have c1 : ((D.R.m - (i : ℕ) - 1 : ℕ) : ℝ) = D.R.m - (i : ℕ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    have c2 : ((D.R.m - (i : ℕ) : ℕ) : ℝ) = D.R.m - (i : ℕ) := by
      rw [Nat.cast_sub (by omega)]
    push_cast
    rw [c1, c2]
    have hv'' : ((G0.v 2 : ℤ) : ℝ) ≤ large₂.Sc := by exact_mod_cast hv
    nlinarith [mul_le_mul_of_nonneg_right hi' hg0]
  have hc : ((cen D 1 τ (D.R.m - i) : ℤ) : ℝ) ≤ large₂.sc.b := by
    have h1 : ((cen D 1 τ (D.R.m - i) : ℤ) : ℚ) ≤ G0.mid (D.R.m - i) := Int.floor_le _
    have h2 : ((cen D 1 τ (D.R.m - i) : ℤ) : ℝ) ≤ ((G0.mid (D.R.m - i) : ℚ) : ℝ) := by exact_mod_cast h1
    linarith
  linarith

end GlobalTheory.SqTop.SizesBound

namespace GlobalTheory.SqTop.SizesBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sizes (c : ℝ) : GBig fun {D} _ _ {sc} G _ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    c * (Module.finrank ℚ D.host.E : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((kap D sc.cGap i j s τ : ℝ) + s)) ≤ bTH D C x b := by
  refine ⟨0, fun ε CF _ => ⟨2 * |c| + 100, 3, fun C hC D large₂ _ hx hR T Lc μ₀ _ G i j s _ hs => ?_⟩⟩
  have hS := hR.size
  obtain ⟨-, hSA, -, -, -, -, -, hgL, hqL, hrd, hcd, -, -, -⟩ := hR.size
  have hpde : Real.log (D.host.pde : ℝ) ≤ large₂.sc.L ∧ Real.log (D.host.pde' : ℝ) ≤ large₂.sc.L :=
    hSA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

  have hx1 : 1 < large₂.sc.x := by linarith
  have hLpos : 0 < large₂.sc.L := Real.rpow_pos_of_pos (by linarith) _
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp hLpos.le
  have hlx : 1 ≤ Real.log large₂.sc.x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _

  have h1 : c * (Module.finrank ℚ D.host.E : ℝ) ≤ 2 * |c| * D.R.f := by
    rw [Formalism.L2.Pj.hostSize_finrank D]; push_cast
    nlinarith [le_abs_self c]

  have h2 : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * large₂.sc.L := by
    have e : Real.log |((discr D.host.E : ℤ) : ℝ)| = logdE D := rfl
    rw [e, Formalism.BasicNotions.logdE_eq_rd]
    have : Real.log D.host.rdE ≤ large₂.sc.L := by linarith
    nlinarith

  have h3 : Real.log (levQ G.pl) ≤ 2 * D.R.f * (21 * large₂.sc.L + 2) := by
    have hle := levQ_le G.pl
    rw [NumberField.RingOfIntegers.rank, GlobalTheory.ColClassCompare.finrank_F] at hle
    have hpos : 0 < levQ G.pl := Finset.prod_pos fun v _ =>
      pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
    have hle' : (levQ G.pl : ℝ) ≤ ((((D.host.g 0 : ℕ) : ℝ) * (D.host.g 1 : ℕ) * (D.host.pde : ℕ) * (D.host.pde' : ℕ) *
        (q0 D : ℕ)) ^ D.R.f) ^ 2 := by exact_mod_cast hle
    have hl := Real.log_le_log (by exact_mod_cast hpos) hle'
    have p0 := (D.host.g_prime 0).pos
    have p1 := (D.host.g_prime 1).pos
    have p2 := D.host.pde_prime.pos
    have p3 := D.host.pde'_prime.pos
    have p4 := (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
    push_cast at hl
    rw [Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)] at hl
    have g0 := hgL 0
    have g1 := hgL 1
    push_cast at hl
    nlinarith

  have h4 : ∑ τ, Real.log (1 + ((kap D (⟨1, CF, large₂.sc.b⟩ : Consts).cGap i j s τ : ℝ) + s)) ≤
      D.R.f * (5 + large₂.sc.L) := by
    have hk : ∀ τ, Real.log (1 + ((kap D 1 i j s τ : ℝ) + s)) ≤ 5 + large₂.sc.L := by
      intro τ
      have k1 := kap_add_le large₂ hS i j hs τ
      have k0 : (0 : ℝ) ≤ (kap D 1 i j s τ : ℝ) + s := by positivity
      calc Real.log (1 + ((kap D 1 i j s τ : ℝ) + s)) ≤ Real.log (6 * large₂.sc.b) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 6 + large₂.sc.L := by rw [Real.log_mul (by norm_num) (by linarith), hlogb]
        _ ≤ 5 + large₂.sc.L := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)
          linarith
    calc _ ≤ ∑ _τ : D.what₂.Tau, (5 + large₂.sc.L) := Finset.sum_le_sum fun τ _ => hk τ
      _ = D.R.f * (5 + large₂.sc.L) := by
        rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]

  show _ ≤ C * D.R.f * large₂.sc.b * (Real.log large₂.sc.b + Real.log large₂.sc.x)
  rw [hlogb]
  have hC0 : 0 ≤ C := by have := abs_nonneg c; linarith
  have t1 : (2 * |c| + 100) * D.R.f * (large₂.sc.L + 1) ≤ C * D.R.f * (large₂.sc.L + 1) := by
    have : 0 ≤ (D.R.f : ℝ) * (large₂.sc.L + 1) := by positivity
    nlinarith
  have t2 : large₂.sc.L + 1 ≤ large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x) := by nlinarith
  have t3 : C * D.R.f * (large₂.sc.L + 1) ≤ C * D.R.f * (large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x)) :=
    mul_le_mul_of_nonneg_left t2 (by positivity)
  have t4 : 0 ≤ (D.R.f : ℝ) * large₂.sc.L := by positivity
  have t5 : 0 ≤ |c| * D.R.f := by positivity
  nlinarith

end GlobalTheory.SqTop.SizesBound

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSizesLogBoundStatement

section

@[expose] public section

open NumberField GlobalTheory.SqTop GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid

theorem _root_.GlobalTheory.T.gridSizes_log_bound : ∀ c : ℝ, GBig fun {D} _ _ {sc} G _ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    c * (Module.finrank ℚ D.host.E : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((kap D sc.cGap i j s τ : ℝ) + s)) ≤ bTH D C x b := by
  first | exact @GlobalTheory.SqTop.SizesBound.sizes | exact GlobalTheory.SqTop.SizesBound.sizes | (intros; apply GlobalTheory.SqTop.SizesBound.sizes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLValueUpperBoundPermutedWeightsOfFE

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.SqTop GlobalTheory.FunObj GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid Formalism.IndefR.Links

namespace GlobalTheory.SqTop

theorem lBound_of : GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LBound := by
  intro hFE hS hFD
  set c : ℝ := max 0 (Real.log ‖riemannZeta (3 / 2)‖) with hc
  obtain ⟨CF1, hB⟩ := GlobalTheory.T.gridSizes_log_bound c
  obtain ⟨CF2, hF⟩ := hFD
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, hB⟩ := hB ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, hF⟩ := hF ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ hL G => ?_⟩
  have hb := hB C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hL G
  obtain ⟨hCM, hAb, hFd, hBase, -⟩ := hF C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hL G
  intro i j s hs1 hs2 π χ Λ hχ hΛ
  set κ := kap D (⟨1, CF, large₂.sc.b⟩ : Consts).cGap i j s with hκ
  set n : ℕ := Module.finrank ℚ D.host.E with hn
  have key : c * (n : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((κ τ : ℝ) + s)) ≤ bTH D C large₂.sc.x large₂.sc.b := hb i j s hs1 hs2
  have hc0 : 0 ≤ c := le_max_left _ _
  have hcz : Real.log ‖riemannZeta (3 / 2)‖ ≤ c := le_max_right _ _
  have hd0 : 0 ≤ Real.log |((discr D.host.E : ℤ) : ℝ)| := Real.log_nonneg (by
    have := Int.one_le_abs (NumberField.discr_ne_zero D.host.E); exact_mod_cast this)
  have hq0 : 0 ≤ Real.log (levQ G.pl : ℝ) := Real.log_natCast_nonneg _
  have hk0 : 0 ≤ ∑ τ, Real.log (1 + ((κ τ : ℝ) + s)) :=
    Finset.sum_nonneg fun τ _ => Real.log_nonneg (by have : (0:ℝ) ≤ κ τ := Nat.cast_nonneg _; have : (0:ℝ) ≤ s := Nat.cast_nonneg _; linarith)
  have hn0 : (0 : ℝ) ≤ c * n := mul_nonneg hc0 (Nat.cast_nonneg _)
  by_cases h0 : Λ s = 0
  · rw [h0, norm_zero, Real.log_zero]
    linarith
  have hpos : 0 < ‖Λ s‖ := norm_pos_iff.2 h0
  have hz : 0 < ‖riemannZeta (3 / 2)‖ := norm_pos_iff.2 (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  rcases (by omega : s = 1 ∨ 2 ≤ s) with rfl | h2
  · obtain ⟨a, ha, haN⟩ := GlobalTheory.T.exists_cmValueCharacter_conductorExponents D G 1 _ χ hχ
    have hA := GlobalTheory.T.norm_completedHeckeL_CM_one_le_phragmenLindelof D.host.E D.what₂.Tau (cmPhi D) hFE hS hFd.2.2.2.2.2.2.1 χ (fun τ => ((κ (π τ) : ℕ) : ℤ) + ((1 : ℕ) : ℤ)) a Λ
      hχ.1 hχ.2.1 hχ.2.2.1 (fun τ => by positivity) ha hΛ
    simp only [Nat.cast_one] at hpos h0 ⊢
    set N : ℕ := (discr D.host.E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k with hN
    set P : ℝ := ∏ τ, (1 + ((((κ (π τ) : ℕ) : ℤ) + ((1 : ℕ) : ℤ) : ℤ) : ℝ)) with hP
    have hP0 : 0 < P := Finset.prod_pos fun τ _ => by push_cast; positivity
    have hN0 : (0 : ℝ) < N := by
      by_contra hc'
      have : (N : ℝ) = 0 := le_antisymm (not_lt.1 hc') (Nat.cast_nonneg _)
      rw [this, mul_zero, zero_mul] at hA
      linarith
    have hNle : (N : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| * (levQ G.pl : ℝ) ^ 2 := by
      rw [hN, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact_mod_cast haN
    have hQ0 : (0 : ℝ) < levQ G.pl := by
      by_contra hc'
      have : (levQ G.pl : ℝ) = 0 := le_antisymm (not_lt.1 hc') (Nat.cast_nonneg _)
      rw [this, zero_pow two_ne_zero, mul_zero] at hNle; linarith
    have hD0 : (0 : ℝ) < |((discr D.host.E : ℤ) : ℝ)| := by
      have := Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
      have : (1 : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| := by exact_mod_cast this
      linarith
    have h1 : Real.log ‖Λ 1‖ ≤ Real.log (‖riemannZeta (3 / 2)‖ ^ n) + Real.log N + Real.log P := by
      rw [← Real.log_mul (by positivity) hN0.ne', ← Real.log_mul (by positivity) hP0.ne']
      exact Real.log_le_log hpos hA
    have h2 : Real.log N ≤ Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) := by
      calc Real.log N ≤ Real.log (|((discr D.host.E : ℤ) : ℝ)| * (levQ G.pl : ℝ) ^ 2) := Real.log_le_log hN0 hNle
        _ = _ := by rw [Real.log_mul hD0.ne' (by positivity), Real.log_pow]; push_cast; ring
    have h3 : Real.log P = ∑ τ, Real.log (1 + ((κ τ : ℝ) + ((1 : ℕ) : ℝ))) := by
      rw [hP, Real.log_prod (fun τ _ => by push_cast; positivity)]
      rw [← Equiv.sum_comp π (fun τ => Real.log (1 + ((κ τ : ℝ) + ((1 : ℕ) : ℝ))))]
      refine Finset.sum_congr rfl fun τ _ => ?_
      push_cast; ring_nf
    have h4 : Real.log (‖riemannZeta (3 / 2)‖ ^ n) ≤ c * n := by
      rw [Real.log_pow]; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith
  · have h := GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow D.host.E χ Λ s hχ.1 hΛ (by
      simp only [Complex.natCast_re]; have : (2 : ℝ) ≤ s := by exact_mod_cast h2
      linarith)
    have h4 : Real.log ‖Λ s‖ ≤ c * n := by
      calc Real.log ‖Λ s‖ ≤ Real.log (‖riemannZeta (3 / 2)‖ ^ n) := Real.log_le_log hpos h
        _ = n * Real.log ‖riemannZeta (3 / 2)‖ := Real.log_pow _ _
        _ ≤ c * n := by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith

end GlobalTheory.SqTop

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLValueUpperBoundPermutedWeightsOfFEStatement

section

@[expose] public section

open GlobalTheory.SqTop

theorem _root_.GlobalTheory.T.heckeLValue_upperBound_permutedWeights_of_FE : GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LBound := by
  first | exact @GlobalTheory.SqTop.lBound_of | exact GlobalTheory.SqTop.lBound_of | (intros; apply GlobalTheory.SqTop.lBound_of <;> assumption)
end
end
