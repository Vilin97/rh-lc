module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepOfFrobeniusFixedFrameChange
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
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
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicPeriodLocalPrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegreeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitCont

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Pst

namespace GlobalTheory.LTChar

variable {l : ℕ} [Fact l.Prime]

theorem orbit_cont (y : ℂ_[l]) : Continuous fun g : GQ l => Formalism.Per.σC g y := by
  apply GlobalTheory.PMon.FrameChange.cont_σC <;> assumption

end GlobalTheory.LTChar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterFiltrationOne

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.LTChar

theorem char_cont : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (x : P.R.B), P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → ∀ (c : ↥(GK K) → ↥(MaximalUnramifiedExtension l)), (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c g) * x) → Continuous fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  intro l _ P AI T K x h1 h2 c hc
  obtain ⟨-, -, hsh, -, -, -, -, hact, -⟩ := GlobalTheory.PMon.bdR_tied l P AI T
  obtain ⟨S, θ, hS, -, hker, hOm, hθ⟩ := GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt l P AI T
  have hu0 : tz P (-1) * P.ιB x ∈ Fil P 0 := by
    have := (hsh 1 (-1) _).1 h1
    simpa using this
  have hu1 : tz P (-1) * P.ιB x ∉ Fil P 1 := by
    intro h
    apply h2
    rw [hsh 2 (-1)]
    simpa using h
  set u : S := ⟨tz P (-1) * P.ιB x, (hS _).2 hu0⟩ with hu
  have hy : θ u ≠ 0 := fun h => hu1 ((hker u).1 h)
  have key : ∀ g : ↥(GK K), (((c g : ↥(MaximalUnramifiedExtension l)) : Om l) : ℂ_[l]) =
      algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) * Formalism.Per.σC (g : GQ l) (θ u) / θ u := by
    intro g
    obtain ⟨hg, hg'⟩ := hθ g u
    obtain ⟨ha, ha'⟩ := hOm (algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]))
    obtain ⟨hb, hb'⟩ := hOm ((c g : ↥(MaximalUnramifiedExtension l)) : Om l)
    have e : (⟨_, ha⟩ : S) * ⟨_, hg⟩ = ⟨_, hb⟩ * u := by
      apply Subtype.ext
      show algebraMap (Om l) P.R.BdR _ * P.actQdR g (tz P (-1) * P.ιB x) = kd P (c g) * (tz P (-1) * P.ιB x)
      rw [map_mul, hact, ← iota_act, hc, map_mul, iota_kur, ← IsScalarTower.algebraMap_apply, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← map_mul, ← Units.val_mul]
      simp only [zpow_neg, zpow_one, mul_inv_cancel, Units.val_one, map_one]
      ring
    have e' := congrArg θ e
    rw [map_mul θ, map_mul θ, ha', hb', hg'] at e'
    rw [eq_div_iff hy, ← e']
    rfl
  have hemb : Topology.IsEmbedding (fun y : Om l => (y : ℂ_[l])) :=
    UniformSpace.Completion.coe_isometry.isEmbedding
  refine hemb.continuous_iff.2 ?_
  have : ((fun y : Om l => (y : ℂ_[l])) ∘ fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l)) = _ := funext key
  rw [this]
  refine Continuous.div_const (Continuous.mul ?_ ?_) _
  · exact (continuous_algebraMap ℚ_[l] ℂ_[l]).comp
      ((GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val)
  · exact (orbit_cont (θ u)).comp continuous_subtype_val

end GlobalTheory.LTChar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterFiltrationOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.continuous_galois_character_filtration_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (x : P.R.B), P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → ∀ (c : ↥(GK K) → ↥(MaximalUnramifiedExtension l)), (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c g) * x) → Continuous fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  first | exact @GlobalTheory.LTChar.char_cont | exact GlobalTheory.LTChar.char_cont | (intros; apply GlobalTheory.LTChar.char_cont <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodConjRatioUnramified

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon



theorem lt_period_conj_ratio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (s : ℕ), 0 < s → ∀ (x : P.R.B), IsUnit x → P.φB^[s] x = (l : P.R.B) * x → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → ∀ g : GQ l, ∃ a : ↥(MaximalUnramifiedExtension l), fr l s a = a ∧ P.actQ g x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a * x := by
  intro l _ P AI T s hs x hx hφ h1 h2 hj g
  obtain ⟨-, -, hsh, hinv, -, -, -, htz, tadd, t0, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  have iter_mul : ∀ (m : ℕ) (a b : P.R.B), P.φB^[m] (a * b) = P.φB^[m] a * P.φB^[m] b := by
    intro m a b
    induction m generalizing a b with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_mul]
  have iter_one : ∀ m : ℕ, P.φB^[m] (1 : P.R.B) = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, map_one]
  have iter_act : ∀ (m : ℕ) (b : P.R.B), P.φB^[m] (P.actQ g b) = P.actQ g (P.φB^[m] b) := by
    intro m b
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, phiB_actQ]
  have ev_mul : ∀ (m : ℕ) (a b : P.R.B), ev P m (a * b) = ev P m a * ev P m b := by
    intro m a b
    rw [← evHom_apply, map_mul, evHom_apply, evHom_apply]
  obtain ⟨w, hw⟩ : ∃ w : P.R.B, x * w = 1 := ⟨_, hx.mul_val_inv⟩
  set y := P.actQ g x * w with hy
  have hyx : y * x = P.actQ g x := by rw [hy, mul_assoc, mul_comm w x, hw, mul_one]

  have hfix : P.φB^[s] y = y := by
    have e1 : P.φB^[s] x * P.φB^[s] w = 1 := by rw [← iter_mul, hw, iter_one]
    rw [hφ] at e1
    rw [hy, iter_mul, iter_act, hφ, map_mul, map_natCast]
    calc (l : P.R.B) * P.actQ g x * P.φB^[s] w = P.actQ g x * (((l : P.R.B) * x * P.φB^[s] w) * w) := by
          linear_combination (-(l : P.R.B) * P.actQ g x * P.φB^[s] w) * hw
      _ = P.actQ g x * w := by rw [e1, one_mul]

  have key : ∀ (k : ℤ) (e u v z : P.R.BdR), e = tz P k * u → u * v = 1 → u ∈ Fil P 0 → v ∈ Fil P 0 →
      z * e = P.actQdR g e → z ∈ Fil P 0 := by
    intro k e u v z he huv hu hv hz
    have hk : tz P k * tz P (-k) = 1 := by rw [← tadd, add_neg_cancel, t0]
    have hz' : z * e = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * tz P k * P.actQdR g u := by
      rw [hz, he, map_mul, htz]
    have hzz : z = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * P.actQdR g u * v := by
      linear_combination (-z + algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * P.actQdR g u * v) * hk
        - z * tz P k * tz P (-k) * huv - tz P (-k) * v * z * he + tz P (-k) * v * hz'
    rw [hzz]
    exact Fil_mul_right (Fil_mul_left (q_mem_Fil P _) (Fil_act g hu)) hv
  have hev : ∀ j, ev P j y * ev P j x = P.actQdR g (ev P j x) := by
    intro j
    rw [← ev_mul, hyx, ev_act]
  have hfil : ∀ j < s, ev P j y ∈ Fil P 0 := by
    intro j hjs
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · have hu0 : tz P (-1) * P.ιB x ∈ Fil P 0 := by
        have := (hsh 1 (-1) (P.ιB x)).1 h1
        rwa [show (1 : ℤ) + -1 = 0 by norm_num] at this
      have hu1 : tz P (-1) * P.ιB x ∉ Fil P 1 := by
        intro h
        apply h2
        exact (hsh 2 (-1) (P.ιB x)).2 (by rw [show (2 : ℤ) + -1 = 1 by norm_num]; exact h)
      obtain ⟨v, hv, huv⟩ := hinv _ hu0 hu1
      refine key 1 (ev P 0 x) _ v _ ?_ huv hu0 hv (hev 0)
      change P.ιB x = tz P 1 * (tz P (-1) * P.ιB x)
      rw [← mul_assoc, ← tadd, show (1 : ℤ) + -1 = 0 by norm_num, t0, one_mul]
    · obtain ⟨e0, e1⟩ := hj j hpos hjs
      obtain ⟨v, hv, huv⟩ := hinv _ e0 e1
      exact key 0 (ev P j x) (ev P j x) v _ (by rw [t0, one_mul]) huv e0 hv (hev j)
  obtain ⟨a, ha, hya⟩ := GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero l P AI T s hs y hfix hfil
  exact ⟨a, ha, by rw [← hyx, hya]⟩

end GlobalTheory.PMon

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodConjRatioUnramifiedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.lubinTate_period_conj_ratio_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (s : ℕ), 0 < s → ∀ (x : P.R.B), IsUnit x → P.φB^[s] x = (l : P.R.B) * x → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → ∀ g : GQ l, ∃ a : ↥(MaximalUnramifiedExtension l), fr l s a = a ∧ P.actQ g x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a * x := by
  first | exact @GlobalTheory.PMon.lt_period_conj_ratio | exact GlobalTheory.PMon.lt_period_conj_ratio | (intros; apply GlobalTheory.PMon.lt_period_conj_ratio <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateCharacterUnramifiedPeriod

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.LTChar.main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (s : ℕ), 0 < s → ∃ (K' : FinExt l) (_ : K.1 ≤ K'.1) (x : P.R.Bˣ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ), (∀ c : ↥(MaximalUnramifiedExtension l), fr l s c = c → (c : Om l) ∈ K'.1) ∧ (∀ g, fr l s (χ g : ↥(MaximalUnramifiedExtension l)) = χ g) ∧ (Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) ∧ P.ιB x ∈ Fil P 1 ∧ P.ιB x ∉ Fil P 2 ∧ ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := by
  intro l _ P AI T K s hs
  obtain ⟨E, ω, -, -, hE, -⟩ := GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l s hs
  obtain ⟨x, hu, hφ, h1, h2, hj⟩ := GlobalTheory.LTPeriod.main l P AI T K s hs
  have h1' : P.ιB x ∈ Fil P 1 := (mem_Fil_iff P K).2 h1
  have h2' : P.ιB x ∉ Fil P 2 := fun h => h2 ((mem_Fil_iff P K).1 h)
  have hj' : ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := fun j h0 hjs =>
    ⟨(mem_Fil_iff P K).2 (hj j h0 hjs).1, fun h => (hj j h0 hjs).2 ((mem_Fil_iff P K).1 h)⟩
  let K' : FinExt l := supExt K E
  have hKK' : K.1 ≤ K'.1 := le_sup_left
  have hEK' : E.1 ≤ K'.1 := le_sup_right
  choose a ha hax using fun g : GQ l => GlobalTheory.T.lubinTate_period_conj_ratio_unramified l P AI T s hs x hu hφ h1' h2' hj' g
  have hx0 : x ≠ 0 := by
    intro h0
    apply h2'
    rw [h0, map_zero]
    exact Fil_zero_mem 2
  haveI : Nontrivial P.R.B := ⟨⟨x, 0, hx0⟩⟩
  have hcancel : ∀ c c' : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c * x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c' * x → c = c' :=
    fun c c' h => (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (hu.mul_right_cancel h)
  have hfix : ∀ (g : ↥(GK K')) (h : GQ l), P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h)) =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) := fun g h => act_kur P g (hEK' ((hE (a h)).1 (ha h)))
  have hmul : ∀ g h : ↥(GK K'), a ((g : GQ l) * (h : GQ l)) = a g * a h := by
    intro g h
    apply hcancel
    calc algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a ((g : GQ l) * (h : GQ l))) * x = P.actQ ((g : GQ l) * (h : GQ l)) x := (hax _).symm
      _ = P.actQ (g : GQ l) (P.actQ (h : GQ l) x) := by rw [map_mul, AlgEquiv.mul_apply]
      _ = P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) * x) := by rw [hax]
      _ = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) * (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a g) * x) := by rw [map_mul, hfix, hax]
      _ = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a g * a h) * x := by rw [map_mul]; ring
  have hone : a 1 = 1 := by
    apply hcancel
    rw [← hax, map_one, AlgEquiv.one_apply, map_one, one_mul]
  have hne : ∀ g, a g ≠ 0 := by
    intro g h0
    have h := hax g
    rw [h0, map_zero, zero_mul] at h
    exact hx0 ((P.actQ g).injective (h.trans (map_zero _).symm))
  let χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ :=
    { toFun := fun g => Units.mk0 (a g) (hne g)
      map_one' := Units.ext hone
      map_mul' := fun g h => Units.ext (hmul g h) }
  refine ⟨K', hKK', hu.unit, χ, fun c hc => hEK' ((hE c).1 hc), fun g => ha _, ?_, fun g => ?_, ?_, ?_,
    fun j h0 hjs => ?_⟩
  · exact GlobalTheory.T.continuous_galois_character_filtration_one l P AI T K' x h1' h2' (fun g => a g) (fun g => hax g)
  · rw [IsUnit.unit_spec]
    exact hax g
  · rw [IsUnit.unit_spec]
    exact h1'
  · rw [IsUnit.unit_spec]
    exact h2'
  · rw [IsUnit.unit_spec]
    exact hj' j h0 hjs

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateCharacterUnramifiedPeriodStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_lubinTate_character_unramified_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (s : ℕ), 0 < s → ∃ (K' : FinExt l) (_ : K.1 ≤ K'.1) (x : P.R.Bˣ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ), (∀ c : ↥(MaximalUnramifiedExtension l), fr l s c = c → (c : Om l) ∈ K'.1) ∧ (∀ g, fr l s (χ g : ↥(MaximalUnramifiedExtension l)) = χ g) ∧ (Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) ∧ P.ιB x ∈ Fil P 1 ∧ P.ιB x ∉ Fil P 2 ∧ ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := by
  first | exact @GlobalTheory.LTChar.main | exact GlobalTheory.LTChar.main | (intros; apply GlobalTheory.LTChar.main <;> assumption)
end
end
