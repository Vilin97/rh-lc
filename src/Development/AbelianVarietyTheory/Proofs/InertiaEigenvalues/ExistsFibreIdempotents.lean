module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostFieldStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenKernelIdeleCharacterTrivialFinitePartOne
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceTwistTrivialOnCongruentUnits

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open GlobalTheory.ExportSeries

namespace GlobalTheory.OnePlaceCong

def locU {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) : Rˣ where
  val := 1 - g + g * x
  inv := 1 - g + g * (x⁻¹ : Rˣ)
  val_inv := by
    have h := x.mul_inv
    linear_combination (-((x : R) + (x⁻¹ : Rˣ) - 2)) * hg + g * g * h
  inv_val := by
    have h := x.inv_mul
    linear_combination (-((x : R) + (x⁻¹ : Rˣ) - 2)) * hg + g * g * h

theorem coe_locU {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) :
    ((locU g hg x : Rˣ) : R) = 1 - g + g * x := rfl

theorem locU_inv {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) :
    (locU g hg x)⁻¹ = locU g hg x⁻¹ := rfl

variable {D : D7}

theorem finPart_locU_mem {g : AE D} (hg : g * g = g) {z : (AE D)ˣ} (hz : finPart D (z : AE D) ∈ intAE D) :
    finPart D ((locU g hg z : (AE D)ˣ) : AE D) ∈ intAE D := by
  have h1 : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1)
  have hfg : finPart D g ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hg])
  rw [coe_locU, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul]
  exact add_mem (sub_mem h1 hfg) (GlobalTheory.HeckeConj.mul_mem_intAE D hfg hz)

theorem res_locU_eq_one {A : Type} [CommGroup A] {PP : Pl D.host.E} {χ : (AE D)ˣ →* A} {c : (kP PP)ˣ →* A}
    (hχ : IsResAt χ PP c) (hI : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) (N : ℕ)
    (hN : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (x : (AE D)ˣ) (hx : finPart D (x : AE D) ∈ intAE D)
    (y : Af D.host.F ⊗[D.host.F] D.host.E) (hy : y ∈ intAE D) (hxy : finPart D (x : AE D) - 1 = N • y) :
    χ (locU (idemAt PP) hI.1.1 x) = 1 := by
  have he : idemAt PP * idemAt PP = idemAt PP := hI.1.1
  have hfa := finPart_locU_mem he hx
  have hxa := GlobalTheory.IdemRes.toEAf_mem_of_finPart hfa
  obtain ⟨hE, hres⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (idemAt PP) PP hI
  obtain ⟨w, rfl⟩ := GlobalTheory.SplitDualLat.finPart_surjective (D := D) y
  have hX := GlobalTheory.IdemRes.toEAf_mem_of_finPart hx
  have hW := GlobalTheory.IdemRes.toEAf_mem_of_finPart hy
  have key0 : Formalism.IndefR.Datum.toEAf D ((x : AE D) - 1 - N • w) = 0 := by
    change Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D _) = 0
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul, hxy, sub_self, map_zero]
  have key : Formalism.IndefR.Datum.toEAf D (x : AE D) = 1 + N • Formalism.IndefR.Datum.toEAf D w := by
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul] at key0
    linear_combination key0
  have ha : (⟨Formalism.IndefR.Datum.toEAf D (locU (idemAt PP) he x : AE D), hxa⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      1 - ⟨_, hE⟩ + ⟨_, hE⟩ * (1 + N • ⟨_, hW⟩) := by
    apply Subtype.ext
    change Formalism.IndefR.Datum.toEAf D (1 - idemAt PP + idemAt PP * (x : AE D)) =
      1 - Formalism.IndefR.Datum.toEAf D (idemAt PP) + Formalism.IndefR.Datum.toEAf D (idemAt PP) *
        (1 + N • Formalism.IndefR.Datum.toEAf D w)
    rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul, key]
  have hN0 : ((N : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hN
  refine (hχ _ ?_ hxa 1 ?_).trans (map_one c)
  · change (1 - idemAt PP) * (1 - idemAt PP + idemAt PP * (x : AE D)) = 1 - idemAt PP
    linear_combination (-((x : AE D) - 1)) * he
  · rw [ha, map_add (f := _), map_sub, map_one, map_mul, hres, map_add (f := _), map_one, map_nsmul, nsmul_eq_mul, hN0]
    simp

theorem chi_eq_one_of_cong : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := by
  intro D A _ PP χ κ ht N hN x hx hxy
  obtain ⟨y, hy, hxy⟩ := hxy
  have hPP : PP ∈ ({PP} : Finset (Pl D.host.E)) := Finset.mem_singleton_self PP
  have hsp : SplitSet ({PP} : Finset (Pl D.host.E)) := ht.split
  have hI := hsp.isIdemAt hPP
  have he : idemAt PP * idemAt PP = idemAt PP := hI.1.1
  have h0 : idemAt PP * cA D (idemAt PP) = 0 := hsp.mul_conj hPP hPP
  have hc : cA D (idemAt PP) * cA D (idemAt PP) = cA D (idemAt PP) := by rw [← RingHom.map_mul, he]
  have hg : (1 - idemAt PP - cA D (idemAt PP)) * (1 - idemAt PP - cA D (idemAt PP)) =
      1 - idemAt PP - cA D (idemAt PP) := by
    linear_combination he + hc + 2 * h0
  have hres := ht.res PP hPP

  have hx_eq : x = locU (idemAt PP) he x * locU (cA D (idemAt PP)) hc x *
      locU (1 - idemAt PP - cA D (idemAt PP)) hg x := by
    apply Units.ext
    simp only [Units.val_mul, coe_locU]
    linear_combination ((x : AE D) - 1) ^ 2 * he + ((x : AE D) - 1) ^ 2 * hc +
      (((x : AE D) - 1) ^ 2 - (1 - idemAt PP - cA D (idemAt PP)) * ((x : AE D) - 1) ^ 3) * h0

  have hA : χ (locU (idemAt PP) he x) = 1 := res_locU_eq_one hres hI N hN x hx.2.1 y hy hxy

  have hB : χ (locU (cA D (idemAt PP)) hc x) = 1 := by
    have hcb : Units.map (cA D).toMonoidHom (locU (cA D (idemAt PP)) hc x) =
        locU (idemAt PP) he (Units.map (cA D).toMonoidHom x) := by
      apply Units.ext
      change cA D (1 - cA D (idemAt PP) + cA D (idemAt PP) * (x : AE D)) = 1 - idemAt PP + idemAt PP * cA D (x : AE D)
      rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul, Formalism.L2.Theta.cA_cA]
    have h1 : χ (locU (idemAt PP) he (Units.map (cA D).toMonoidHom x)) = 1 := by
      refine res_locU_eq_one hres hI N hN _ ?_ (sigR (Af D.host.F) D.sp.cm.sig y)
        (GlobalTheory.SplitDualLat.sigR_mem_intAE hy) ?_
      · change finPart D (cA D (x : AE D)) ∈ intAE D
        rw [GlobalTheory.SplitDualLat.finPart_cA]
        exact GlobalTheory.SplitDualLat.sigR_mem_intAE hx.2.1
      · change finPart D (cA D (x : AE D)) - 1 = _
        rw [GlobalTheory.SplitDualLat.finPart_cA, ← RingHom.map_one (sigR (Af D.host.F) D.sp.cm.sig), ← RingHom.map_sub, hxy,
          map_nsmul]
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      intro x
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add (f := _), hσ, add_comm]
    set b := locU (cA D (idemAt PP)) hc x with hb
    have hz : sigR (AF D.host.F) D.sp.cm.sig ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D) =
        ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D) := by
      change cA D ((b : AE D) * cA D (b : AE D)) = (b : AE D) * cA D (b : AE D)
      rw [RingHom.map_mul, Formalism.L2.Theta.cA_cA, mul_comm]
    obtain ⟨a, ha⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr _ hz
    have hr : χ (idF D a) = 1 := ht.real a
    have ha' : idF D a = b * Units.map (cA D).toMonoidHom b := ha
    rw [ha', map_mul, hcb, h1, mul_one] at hr
    exact hr

  have hC : χ (locU (1 - idemAt PP - cA D (idemAt PP)) hg x) = 1 := by
    have hi0 : infPart D (idemAt PP) = 0 := SpecGood.infPart_eq_zero_of_isIdemAt D PP _ hI
    have hi1 : infPart D (cA D (idemAt PP)) = 0 := by
      rw [GlobalTheory.PlaceIdem.infPart_cA, hi0, RingHom.map_zero]
    have hidem : idem ({PP} : Finset (Pl D.host.E)) = idemAt PP := Finset.sum_singleton _ _
    refine ht.unram _ ?_ (finPart_locU_mem hg hx.2.1) ?_ ?_
    · rw [coe_locU, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_sub,
        RingHom.map_one, hi0, hi1, hx.1]
      ring
    · rw [locU_inv]
      exact finPart_locU_mem hg hx.2.2
    · change (idem ({PP} : Finset (Pl D.host.E)) + cA D (idem ({PP} : Finset (Pl D.host.E)))) *
        (1 - (1 - idemAt PP - cA D (idemAt PP)) + (1 - idemAt PP - cA D (idemAt PP)) * (x : AE D)) = _
      rw [hidem]
      linear_combination (-((x : AE D) - 1)) * he + (-((x : AE D) - 1)) * hc + (-2 * ((x : AE D) - 1)) * h0
  rw [hx_eq, map_mul, map_mul, hA, hB, hC, mul_one, mul_one]

end GlobalTheory.OnePlaceCong
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceTwistTrivialOnCongruentUnitsStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.onePlaceTwist_trivial_on_congruent_units : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := by
  first | exact @GlobalTheory.OnePlaceCong.chi_eq_one_of_cong | exact GlobalTheory.OnePlaceCong.chi_eq_one_of_cong | (intros; apply GlobalTheory.OnePlaceCong.chi_eq_one_of_cong <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenKernelIdeleCharacterTrivialFinitePartOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover


theorem _root_.GlobalTheory.T.openKernel_ideleCharacter_trivial_finitePart_one : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A), IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := by
  first | exact @GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one | exact GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one | (intros; apply GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFibreIdempotents

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover

namespace GlobalTheory.FibreIdem

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem chi_eq_one_of_finPart : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A), IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := GlobalTheory.T.openKernel_ideleCharacter_trivial_finitePart_one

theorem chi_eq_one_of_cong : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := GlobalTheory.T.onePlaceTwist_trivial_on_congruent_units

theorem char_root_eq_one' (V : HSp D) {A : Type} [CommGroup A] (c : (AE D)ˣ →* A) (N : ℕ) (hN : Odd N)
    (hF : ∀ a, c (idF D a) = 1) (hinf : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1)
    (hcong : ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1)
    (g : GA D V) (x : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hg : ∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
      (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) : c x = 1 := by
  obtain ⟨w, hw, hwe⟩ := hg
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hwe
  have hn := GlobalTheory.RecDict.det_finHom_norm V g
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  have hcY : c Y = 1 := hcong Y ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩ ⟨p, hp, hY2 ▸ hpe⟩
  have hdet : (finHom V g).1.det = finPart D (matHom V g).1.det := ((finPart D).map_det _).symm
  have hxf : finPart D (x : AE D) =
      (finHom V g).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hdet, ← GlobalTheory.DetRootCong.finPart_sigR, ← RingHom.map_mul]
    exact congrArg _ hx
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom (x * Y⁻¹))
    (GlobalTheory.DetRootCong.quot_fixed (finPart D) _ x Y _ y y' hxf hroot hyy hY3)
  obtain ⟨a, ha⟩ := GlobalTheory.DetRootCong.exists_idF D b
  have hb' : finPart D (idF D a : AE D) = finPart D ((x * Y⁻¹ : (AE D)ˣ) : AE D) :=
    ha.trans (congrArg Units.val hb)
  have h1 := hinf (x * Y⁻¹ * (idF D a)⁻¹) (by
    rw [Units.val_mul, RingHom.map_mul, ← hb', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  simpa [hcY, hF a] using h1

end GlobalTheory.FibreIdem

namespace GlobalTheory.FibreIdem

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

end GlobalTheory.FibreIdem
end
end
