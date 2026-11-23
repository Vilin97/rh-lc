module

public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import GroundTheory.PAdicHodge.WAKummerEps
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.TieQB
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT
public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic
import GroundTheory.PAdicHodge.BdRTGalois
import Mathlib.Algebra.Order.Star.Real
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.TieQB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTied6

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.CoeUntiltIterateLFlat

section

@[expose] public section

noncomputable section

open GroundTheory.PAdicHodge

namespace UpperTheory.Lit.Drps.Kum

variable {l : ℕ} [Fact l.Prime]

local notation "𝒪" => normInteger ℂ_[l]
local notation "𝒪♭" => PreTilt 𝒪 l
local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv 𝒪♭ l)

variable {P : Formalism.BasicNotions.LocPrime l} (AI : Formalism.BasicNotions.LocAinf l P)

def zeta (n : ℕ) : 𝒪 := Formalism.Per6.intEquiv l (AI.ζ n)

theorem zeta_succ (n : ℕ) : zeta AI (n + 1) ^ l = zeta AI n := by
  rw [zeta, ← map_pow, AI.ζ_succ]; rfl

def epsT : 𝒪♭ := IsPerfectoidField.ofCompatible l (zeta AI) (zeta_succ AI)

theorem tiltMap_eps : Formalism.Per6.tiltMap l AI.ε = epsT AI :=
  IsPerfectoidField.preTilt_ext l fun n => by
    rw [epsT, IsPerfectoidField.coeff_ofCompatible, Formalism.Per6.tiltMap]
    show (Formalism.Per6.modPEquiv l) (PreTilt.coeff n AI.ε) = _
    rw [AI.ε_coeff]
    rfl

theorem untilt_epsT : PreTilt.untilt (epsT AI) = 1 := by
  rw [epsT, IsPerfectoidField.untilt_ofCompatible, zeta, AI.ζ_zero, map_one]

theorem coe_pow' (x : PadicAlgCl l) (n : ℕ) : ((x ^ n : PadicAlgCl l) : ℂ_[l]) = (x : ℂ_[l]) ^ n :=
  map_pow (UniformSpace.Completion.coeRingHom (α := PadicAlgCl l)) x n

theorem norm_lRoot_le (m : ℕ) : ‖((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l])‖ ≤ 1 := by
  have h : ‖((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l])‖ ^ (l ^ m) = ‖(((l : PadicAlgCl l)) : ℂ_[l])‖ := by
    rw [← norm_pow, ← coe_pow', GlobalTheory.Pst.lRoot_pow l m]
  have hl : ‖(((l : PadicAlgCl l)) : ℂ_[l])‖ ≤ 1 := by
    have := (IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[l]) (p := l)).le
    simpa using this
  rw [← h] at hl
  by_contra hlt
  push_neg at hlt
  exact absurd hl (not_le.2 (one_lt_pow₀ hlt (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)))

def lRootInt (m : ℕ) : 𝒪 := ⟨((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l]), mem_normInteger.2 (norm_lRoot_le m)⟩

theorem lRootInt_succ (m : ℕ) : lRootInt (l := l) (m + 1) ^ l = lRootInt m :=
  Subtype.ext (by
    show ((GlobalTheory.Pst.lRoot l (m + 1) : PadicAlgCl l) : ℂ_[l]) ^ l = ((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l])
    rw [← GlobalTheory.Pst.lRoot_succ l m, coe_pow'])


variable (l) in
def lFlat : 𝒪♭ := IsPerfectoidField.ofCompatible l lRootInt lRootInt_succ

theorem coe_untilt_iterate_lFlat (n : ℕ) :
    ((PreTilt.untilt (φi^[n] (lFlat l)) : 𝒪) : ℂ_[l]) = ((GlobalTheory.Pst.lRoot l n : PadicAlgCl l) : ℂ_[l]) := by
  rw [lFlat, untilt_iterate_ofCompatible]; rfl

theorem iterate_mul (n : ℕ) (x y : 𝒪♭) : φi^[n] (x * y) = φi^[n] x * φi^[n] y :=
  by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem coe_untilt_mul (x y : 𝒪♭) :
    ((PreTilt.untilt (x * y) : 𝒪) : ℂ_[l]) = ((PreTilt.untilt x : 𝒪) : ℂ_[l]) * ((PreTilt.untilt y : 𝒪) : ℂ_[l]) := by
  rw [map_mul]; rfl

theorem coe_untilt_iterate_epsT (n : ℕ) :
    ((PreTilt.untilt (φi^[n] (epsT AI)) : 𝒪) : ℂ_[l]) = ((P.ζQ n : PadicAlgCl l) : ℂ_[l]) := by
  rw [epsT, untilt_iterate_ofCompatible, zeta]
  exact AI.ζ_eq n

theorem tiltGal_lFlat (g : Formalism.BasicNotions.Loc.GQ l) :
    tiltGal (Formalism.Per6.toBot g) (lFlat l) = lFlat l * epsPow (untilt_epsT AI) (GlobalTheory.Pst.kummer P g) := by
  refine tilt_ext_untilt fun n => Subtype.ext ?_
  show ((PreTilt.untilt (φi^[n] (tiltGal (Formalism.Per6.toBot g) (lFlat l))) : 𝒪) : ℂ_[l]) =
    ((PreTilt.untilt (φi^[n] (lFlat l * epsPow (untilt_epsT AI) (GlobalTheory.Pst.kummer P g))) : 𝒪) : ℂ_[l])
  rw [coe_untilt_iterate_tiltGal, coe_untilt_iterate_lFlat, iterate_mul, coe_untilt_mul, coe_untilt_iterate_lFlat,
    untilt_iterate_epsPow, SubmonoidClass.coe_pow, coe_untilt_iterate_epsT, gal_smul_coe]
  show (((g (GlobalTheory.Pst.lRoot l n) : PadicAlgCl l)) : ℂ_[l]) = _
  rw [GlobalTheory.Pst.isKummer_kummer P g n, mul_comm]
  push_cast [coe_pow']
  rfl

theorem untilt_lFlat : ((PreTilt.untilt (lFlat l) : 𝒪) : ℂ_[l]) = l := by
  have := coe_untilt_iterate_lFlat (l := l) 0
  rw [Function.iterate_zero_apply] at this
  rw [this, GlobalTheory.Pst.lRoot_zero]
  norm_cast

theorem exists_lFlat_eq : ∃ b : ℤ_[l], lFlat l = pFlat l * epsPow untilt_epsilon b := by
  obtain ⟨η, hη⟩ : pFlat l ∣ lFlat l :=
    preTilt_dvd_iff_norm_le.2 (le_of_eq (by rw [preTilt_norm_def, preTilt_norm_def, untilt_lFlat, coe_untilt_pFlat]))
  have hη1 : PreTilt.untilt η = 1 := by
    have h := congrArg (fun y => ((PreTilt.untilt y : 𝒪) : ℂ_[l])) hη
    rw [coe_untilt_mul, untilt_lFlat, coe_untilt_pFlat] at h
    apply Subtype.ext
    rw [OneMemClass.coe_one]
    exact ((mul_eq_left₀ natCast_p_ne_zero_cp).1 h.symm)
  obtain ⟨b, hb⟩ := exists_epsPow_eq untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one hη1
  exact ⟨b, by rw [hη, hb]⟩

theorem exists_epsT_eq : ∃ a : ℤ_[l], epsPow untilt_epsilon a = epsT AI :=
  exists_epsPow_eq untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (untilt_epsT AI)

theorem pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {m : ℕ} (h : x ^ m = 1) (k : ℕ) : x ^ (k % m) = x ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k m, pow_add, pow_mul, h, one_pow, mul_one]

theorem epsPow_epsPow {a : ℤ_[l]} (ha : epsPow untilt_epsilon a = epsT AI) (c : ℤ_[l]) :
    epsPow (untilt_epsT AI) c = epsPow untilt_epsilon (a * c) := by
  refine tilt_ext_untilt fun n => ?_
  have e1 : PreTilt.untilt (φi^[n] (epsT AI)) =
      PreTilt.untilt (φi^[n] (epsilon l)) ^ (PadicInt.toZModPow n a).val := by
    rw [← ha]; exact untilt_iterate_epsPow _ a n
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have e2 : (PadicInt.toZModPow n (a * c)).val = (PadicInt.toZModPow n a).val * (PadicInt.toZModPow n c).val % (l ^ n) := by
    rw [map_mul, ZMod.val_mul]
  have L := untilt_iterate_epsPow (untilt_epsT AI) c n
  have R := untilt_iterate_epsPow (untilt_epsilon (p := l)) (a * c) n
  rw [L, R, e1, ← pow_mul, e2, pow_mod_of_pow_eq_one (untilt_iterate_pow_eq_one (untilt_epsilon (p := l)) n)]

theorem kummer_rel {a b : ℤ_[l]} (ha : epsPow untilt_epsilon a = epsT AI) (hb : lFlat l = pFlat l * epsPow untilt_epsilon b)
    (g : Formalism.BasicNotions.Loc.GQ l) :
    kummerC untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (Formalism.Per6.toBot g) +
      (cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]) * b = b + a * GlobalTheory.Pst.kummer P g := by
  apply epsPow_injective untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one
  apply tilt_mul_left_cancel (pFlat_ne_zero (p := l))
  have h1 := tiltGal_lFlat AI g
  have hp : tiltGal (Formalism.Per6.toBot g) (pFlat l) = pFlat l * kummerEta (Formalism.Per6.toBot g) :=
    pFlat_mul_kummerEta (Formalism.Per6.toBot g)
  rw [hb, map_mul, hp, tiltGal_epsPow, epsPow_epsPow AI ha,
    kummerEta_eq_epsPow untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one, mul_assoc, mul_assoc,
    ← epsPow_add, ← epsPow_add] at h1
  exact h1

theorem fontaineT_congr' {x y : 𝒪♭} (h : x = y) (hx : PreTilt.untilt x = 1) (hy : PreTilt.untilt y = 1) :
    fontaineT x hx = fontaineT y hy := by
  subst h; rfl

theorem exists_rel (T : Formalism.BasicNotions.LocTied6 l P AI) : ∃ a b : ℤ_[l],
    T.eD (P.ιB P.tB) = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)
      (algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (a : ℚ_[l]) * fontaineT (epsilon l) untilt_epsilon) ∧
    ∀ g : Formalism.BasicNotions.Loc.GQ l,
      kummerC untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (Formalism.Per6.toBot g) +
        (cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]) * b = b + a * GlobalTheory.Pst.kummer P g := by
  obtain ⟨a, ha⟩ := exists_epsT_eq AI
  obtain ⟨b, hb⟩ := exists_lFlat_eq (l := l)
  refine ⟨a, b, ?_, kummer_rel AI ha hb⟩
  rw [PositivityTheory.LocInh.tie_t T, ← fontaineT_epsPow,
    fontaineT_congr' ((tiltMap_eps AI).trans ha.symm) _ (untilt_epsPow _ a)]

end UpperTheory.Lit.Drps.Kum
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsBeta

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace UpperTheory.Lit.Drps

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem exists_beta (T : LocTied6 l P AI) : ∃ β : ℚ_[l], ∀ g : GQ l,
    T.eB ((GlobalTheory.Pst.kummer P g : ℚ_[l]) • P.tB) =
      period_ring_base.qB l (period_ring_base.κ g) * period_ring_base.t l +
        (period_ring_base.σB g (period_ring_base.qB l β * period_ring_base.t l) - period_ring_base.qB l β * period_ring_base.t l) := by
  obtain ⟨a, b, ht, hr⟩ := Kum.exists_rel AI T
  have h1 : T.eB P.tB = period_ring_base.qB l (a : ℚ_[l]) * period_ring_base.t l := by
    apply period_ring_base.base_ι_inj l
    rw [map_mul, period_ring_base.base_ι_q, period_ring_base.period_image_eq, period_ring_base.BaseA.ι_eq, ← PositivityTheory.LocInh.tie_ι T, ht, map_mul,
      DeRhamTwist.Twist.tQ_eq]
    rfl
  refine ⟨(b : ℚ_[l]), fun g => ?_⟩
  have h2 : period_ring_base.κ g + period_ring_base.χ g * (b : ℚ_[l]) = b + a * (GlobalTheory.Pst.kummer P g : ℚ_[l]) := by
    have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) (hr g)
    simp only [PadicInt.coe_add, PadicInt.coe_mul] at this
    exact this
  have h3 := congrArg (period_ring_base.qB l) h2
  simp only [map_add (f := _), map_mul] at h3
  rw [Algebra.smul_def, map_mul, period_ring_base.DualB.tie_qB T, h1, map_mul, period_ring_base.base_σ_q, period_ring_base.galois_period_cyclotomic]
  linear_combination (-(period_ring_base.t l)) * h3

end UpperTheory.Lit.Drps
end
end
end

-- Source module: GroundTheory.PAdicHodge.ExistsNormLeOfNormLtOneFinite

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open _root_.WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

variable {p : ℕ} [hp : Fact p.Prime]

section Span

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {K}

end Span

section Contradiction

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt 𝒪 p
local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv 𝒪♭ p)

theorem gal_smul_untilt_iterate_of_eq_mul {ε x : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    {σ : Gal(PadicAlgCl p/K)} {a : ℤ_[p]} (h : tiltGal σ x = x * epsPow hε a) (m : ℕ) :
    σ • ((PreTilt.untilt (φi^[m] x) : 𝒪) : ℂ_[p]) = ((PreTilt.untilt (φi^[m] x) : 𝒪) : ℂ_[p]) *
      ((PreTilt.untilt (φi^[m] ε) : 𝒪) : ℂ_[p]) ^ (PadicInt.toZModPow m a).val := by
  rw [← coe_untilt_iterate_tiltGal, h, iterate_frobSymm_mul, map_mul, untilt_iterate_epsPow,
    MulMemClass.coe_mul, SubmonoidClass.coe_pow]



end Contradiction

end GroundTheory.PAdicHodge
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsCoeEqUntiltPFlat

section

@[expose] public section

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

section cont

variable {l : ℕ} [Fact l.Prime]

local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[l]) l) l)

theorem exists_coe_eq_untilt_pFlat (m : ℕ) : ∃ z : PadicAlgCl l,
    (z : ℂ_[l]) = ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) := by
  have hN : l ^ m ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (l : PadicAlgCl l) (Nat.pos_of_ne_zero hN)
  have hπ : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ^ l ^ m = (l : ℂ_[l]) := by
    rw [← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, coe_untilt_pFlat]
  have hyl : algebraMap (PadicAlgCl l) ℂ_[l] y ^ l ^ m = (l : ℂ_[l]) := by
    rw [← map_pow, hy, map_natCast]
  have hy0 : algebraMap (PadicAlgCl l) ℂ_[l] y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN] at hyl
    exact natCast_p_ne_zero_cp (p := l) hyl.symm
  obtain ⟨w, hw⟩ := exists_coe_eq_of_pow_eq_one hN
    (x := ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) * (algebraMap (PadicAlgCl l) ℂ_[l] y)⁻¹)
    (by rw [mul_pow, inv_pow, hπ, hyl, mul_inv_cancel₀ (natCast_p_ne_zero_cp (p := l))])
  refine ⟨y * w, ?_⟩
  change algebraMap (PadicAlgCl l) ℂ_[l] (y * w) = _
  rw [map_mul, show algebraMap (PadicAlgCl l) ℂ_[l] w = _ from hw, mul_comm, mul_assoc, inv_mul_cancel₀ hy0,
    mul_one]

theorem toZModPow_kummerC_eq (m : ℕ) {g h : GQ l} {z : PadicAlgCl l}
    (hz : (z : ℂ_[l]) = ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l])) (hgh : h z = g z) :
    PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot h)) =
      PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g)) := by
  have e : ∀ σ : GQ l, (toBot σ) • ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) =
      ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) *
        ((PreTilt.untilt (φi^[m] (epsilon l)) : normInteger ℂ_[l]) : ℂ_[l]) ^
          (PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one
            (toBot σ))).val := fun σ =>
    gal_smul_untilt_iterate_of_eq_mul untilt_epsilon
      (tiltGal_eq_mul_epsPow untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one pFlat_ne_zero
        gal_smul_coe_untilt_pFlat (toBot σ)) m
  have hs : ∀ σ : GQ l, (toBot σ) • ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) =
      ((σ z : PadicAlgCl l) : ℂ_[l]) := fun σ => by
    rw [← hz, ← galCp_apply, galCp_coe]
    rfl
  have hπ0 : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ≠ 0 := by
    intro h0
    have hπ : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ^ l ^ m = (l : ℂ_[l]) := by
      rw [← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, coe_untilt_pFlat]
    rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hπ
    exact natCast_p_ne_zero_cp (p := l) hπ.symm
  have h2 := (e h).symm.trans ((hs h).trans (hgh ▸ (hs g).symm |>.trans (e g)))
  have h3 := mul_left_cancel₀ hπ0 h2
  have hprim : IsPrimitiveRoot ((PreTilt.untilt (φi^[m] (epsilon l)) : normInteger ℂ_[l]) : ℂ_[l]) (l ^ m) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.2
      (isPrimitiveRoot_untilt_iterate untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one m)
  exact ZMod.val_injective _ (hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

end cont

theorem continuous_κ (l : ℕ) [Fact l.Prime] : Continuous (κ : GQ l → ℚ_[l]) := by
  have hc : Continuous fun g : GQ l =>
      kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g) := by
    refine continuous_iff_continuousAt.2 fun g0 => Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l))
    obtain ⟨z, hz⟩ := exists_coe_eq_untilt_pFlat (l := l) m
    have : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {z}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    have hU : IsOpen {h : GQ l | g0⁻¹ * h ∈ (IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup} :=
      (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const_mul _)
    have h1 : g0 ∈ {h : GQ l | g0⁻¹ * h ∈ (IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup} := by
      simp only [Set.mem_ofPred_eq, inv_mul_cancel]
      exact Subgroup.one_mem _
    filter_upwards [hU.mem_nhds h1] with h hh
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh z (IntermediateField.mem_adjoin_simple_self _ _)
    have hgh : h z = g0 z := by
      have := congrArg g0 hfix
      simpa using this
    have e := toZModPow_kummerC_eq m hz hgh
    rw [dist_eq_norm]
    have hmem : kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot h) -
        kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g0) ∈
          Ideal.span {(l : ℤ_[l]) ^ m} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, e, sub_self]
    calc _ ≤ (l : ℝ) ^ (-(m : ℤ)) := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hmem
      _ = (l : ℝ)⁻¹ ^ m := by rw [_root_.zpow_neg, zpow_natCast, inv_pow]
      _ < ε := hm
  exact continuous_subtype_val.comp hc

end period_ring_base
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.BasedP

section

@[expose] public section

noncomputable section

namespace period_ring_base

open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

theorem base_κ_cont (l : ℕ) [Fact l.Prime] : Continuous (κ : GQ l → ℚ_[l]) := continuous_κ l

theorem base_no_kummer (l : ℕ) [Fact l.Prime] : ∀ L : Fld l, FiniteDimensional ℚ_[l] L → ∀ x : B l,
    ¬ ∀ σ ∈ L.fixingSubgroup, σB σ x - x = qB l (κ σ) * t l := by
  intro L hL x h
  obtain ⟨P, AI, ⟨T0⟩⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  obtain ⟨T⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI ⟨T0⟩
  obtain ⟨β, hβ⟩ := UpperTheory.Lit.Drps.exists_beta T
  have := GlobalTheory.Pst.nontrivial_B P
  apply GlobalTheory.Pst.StLat.kummer_not_frac l P AI T0 ⟨L, hL⟩ 1 (T.eB.symm (x + qB l β * t l)) one_ne_zero
  intro g hg
  apply T.eB.injective
  rw [map_one, one_mul, one_mul, one_mul, one_mul, map_sub, DualB.tie_σB T, RingEquiv.apply_symm_apply, hβ, map_add (f := _),
    ← h g hg]
  ring

end period_ring_base
end
end
end
