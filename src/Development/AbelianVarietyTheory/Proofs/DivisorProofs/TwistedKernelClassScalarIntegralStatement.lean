module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulInvGenusLatticeScalarIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetIdealCoprimeSplitSupportedPointStatement
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRamifiedPlacesHeckeCharacter
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
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralAbsNormPowMulOnId

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.TameHeckeIntegral

open Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit

theorem unitOff_onId (E : Type) [Field E] [NumberField E] (ψ : HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ)
    (n : I → ℤ) (hinf : ψ.HasInf φs n) (ht : ∀ v, ψ.TameAt v) (b : ℕ) (hb : b ≠ 0)
    (hu : ∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) (cc : Ideal (𝓞 E)) (hcc : cc ≠ ⊥)
    (hcop : cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤) :
    UnitOff (Ideal.absNorm cc) ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ) := by
  classical
  have hb0 : (b : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hb
  have hfin : {w | ¬ ψ.UnrAt w}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(b : 𝓞 E)}) (by simpa using hb0)).subset fun w hw => ?_
    have hbw : (b : 𝓞 E) ∈ w.asIdeal := by
      by_contra h
      exact hw (hu w h)
    show w.asIdeal ∣ Ideal.span {(b : 𝓞 E)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hbw
  have hcc0 : cc ≠ 0 := hcc
  unfold HChar.onId
  refine finprod_induction (fun u : ℂˣ => UnitOff (Ideal.absNorm cc) (u : ℂ)) (by simpa using unitOff_one _)
    (fun x y hx hy => by simpa [Units.val_mul] using unitOff_mul hx hy) fun v => ?_
  show UnitOff _ (((ψ.val v ^ FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ)) : ℂ)
  rw [Units.val_zpow_eq_zpow_val]
  by_cases hdv : v.asIdeal ∣ cc
  · have hle : cc ≤ v.asIdeal := Ideal.le_of_dvd hdv
    have hbv : (b : 𝓞 E) ∉ v.asIdeal := fun h => v.isPrime.ne_top (by
      rw [eq_top_iff, ← hcop]
      exact sup_le hle (by rw [Ideal.span_singleton_le_iff_mem]; exact h))
    have hq : ((Ideal.absNorm cc : ℕ) : 𝓞 E) ∈ v.asIdeal := hle (Ideal.absNorm_mem cc)
    exact unitOff_zpow (GlobalTheory.ValUnit.unitOff_val E ψ I φs n v _ hinf hfin ht (hu v hbv) hq) _
  · have h0 : FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 0 := by
      rw [FractionalIdeal.count_coe E v hcc0, Nat.cast_eq_zero]
      by_contra h
      exact hdv ((Associates.count_ne_zero_iff_dvd hcc0 (HeightOneSpectrum.prime v).irreducible).1 h)
    rw [h0, zpow_zero]
    exact unitOff_one _

theorem isIntegral_absNorm_pow_mul_onId : ∀ (E : Type) [Field E] [NumberField E] (ψ : Formalism.L2.Host.HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ) (n : I → ℤ), ψ.HasInf φs n → (∀ v, ψ.TameAt v) → ∀ b : ℕ, b ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) → ∀ cc : Ideal (𝓞 E), cc ≠ ⊥ → cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤ → ∃ K : ℕ, IsIntegral ℤ (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ)) := by
  intro E _ _ ψ I _ φs n hinf ht b hb hu cc hcc hcop
  obtain ⟨_, K, hK, _⟩ := unitOff_onId E ψ I φs n hinf ht b hb hu cc hcc hcop
  exact ⟨K, hK⟩

end GlobalTheory.TameHeckeIntegral
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralAbsNormPowMulOnIdStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.exists_isIntegral_absNorm_pow_mul_onId_of_coprime : ∀ (E : Type) [Field E] [NumberField E] (ψ : Formalism.L2.Host.HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ) (n : I → ℤ), ψ.HasInf φs n → (∀ v, ψ.TameAt v) → ∀ b : ℕ, b ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) → ∀ cc : Ideal (𝓞 E), cc ≠ ⊥ → cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤ → ∃ K : ℕ, IsIntegral ℤ (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId | exact GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId | (intros; apply GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelCharacterIsTameHeckeUnramified

section

@[expose] public section

namespace GlobalTheory.TwistedKernelChar

section General

open NumberField IsDedekindDomain Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem inf_triv [_root_.NumberField.IsTotallyComplex L] (χ : HChar L) {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hpow : ∀ x, χ.1 x ^ n = 1 := fun x => by
    have h1 : (χ ^ n).1 x = 1 := by rw [show χ ^ n = 1 from h]; rfl
    simpa using h1
  show χ.1 (infDiag k) = 1
  rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (atInf w k : w.Completion)) hn
  have hz0 : e.symm z ≠ 0 := by
    intro h0
    have h1 : z = 0 := by simpa using congrArg e h0
    rw [h1, zero_pow hn.ne'] at hz
    exact (atInf w k).ne_zero (e.injective (by rw [← hz, map_zero]))
  have hk : atInf w k = Units.mk0 _ hz0 ^ n := Units.ext (e.injective (by
    rw [← hz, Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, RingEquiv.apply_symm_apply]))
  rw [MonoidHom.comp_apply, hk, map_pow, map_pow, hpow]

theorem hasInf_mul_inv {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n m : I → ℤ} {α β γ : HChar L}
    (ha : α.HasInf φ n) (hb : ∀ k, β.inf k = 1) (hc : γ.HasInf φ m) : (α * β * γ⁻¹).HasInf φ (fun i => n i - m i) := by
  intro k
  rw [HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, hb, mul_one, Units.val_mul, Units.val_inv_eq_inv_val, ha k, hc k,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : φ i (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have h1 : φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero h0 (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 h0))
  rw [zpow_sub₀ h1, div_eq_mul_inv (_ ^ _)]

end General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem frame_char (D : D7) (C : Formalism.L2.Host.CharFrame D) (i : Fin D.R.m) (l : ℕ) :
    ∃ (b : ℕ) (n : D.R.Psi → ℤ), b ≠ 0 ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∈ Q.asIdeal → ((badN D : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → (C.mu0 i * C.delAt l * C.eta⁻¹).UnrAt Q) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q →
        ∀ k : D.host.Fˣ, (C.mu0 i * C.delAt l * C.eta⁻¹).resFin (Q.under (𝓞 D.host.F)) k = 1) ∧
      (∀ Q, (C.mu0 i * C.delAt l * C.eta⁻¹).TameAt Q) ∧
      (C.mu0 i * C.delAt l * C.eta⁻¹).HasInf (Formalism.L2.Host.embPsi D.host) n := by
  classical
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨p, hp, hpl, hδ⟩ : ∃ p : ℕ, p.Prime ∧ p ∈ D.host.levelPrimes ∧ Formalism.L2.Host.IsDelta (H := D.host) p (C.delAt l) := by
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    · exact ⟨_, D.host.pde'_prime, D.host.pde_level.2, C.isDel'⟩
    · exact ⟨_, D.host.pde_prime, D.host.pde_level.1, C.isDel⟩
  have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ∀ a b : ℕ, a ∣ b → (a : 𝓞 D.host.E) ∈ Q.asIdeal →
      (b : 𝓞 D.host.E) ∈ Q.asIdeal := by
    rintro Q a b ⟨u, rfl⟩ h
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  have lev : ∀ a ∈ D.host.levelPrimes, a ∣ badN D := fun a ha =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun p => p) ha) _
  obtain ⟨n, -, hn⟩ := (C.isMu0 i).inf
  obtain ⟨o, ho, hod⟩ := hδ.fin
  refine ⟨D.host.g 0 * D.host.g 1 * p, fun τ => n τ - 1,
    mul_ne_zero (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero) hp.ne_zero, fun Q hQ => ?_,
    fun Q hQ x hx => ?_, fun Q hQ x => ?_, fun Q x hx hx' => ?_,
    hasInf_mul_inv hn (inf_triv _ ho hod) C.isEta.inf⟩
  · rw [Nat.cast_mul, Nat.cast_mul] at hQ
    rcases Q.isPrime.mem_or_mem hQ with h | h
    · rcases Q.isPrime.mem_or_mem h with h | h
      · exact key Q _ _ (lev _ (D.host.g_level 0)) h
      · exact key Q _ _ (lev _ (D.host.g_level 1)) h
    · exact key Q _ _ (lev _ hpl) h
  · have a1 : (C.mu0 i).UnrAt Q := (C.isMu0 i).unr Q fun j hj => hQ (key Q _ _ (by
      refine Dvd.dvd.mul_right ?_ p
      rw [← Fin.prod_univ_two D.host.g]
      exact Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)) hj)
    have a2 : (C.delAt l).UnrAt Q := hδ.unr Q fun hj => hQ (key Q _ _ (Dvd.intro_left _ rfl) hj)
    change (C.mu0 i).loc Q x * (C.delAt l).loc Q x * ((C.eta.loc Q x)⁻¹) = 1
    rw [a1 x hx, a2 x hx,
      C.isEta.unr Q x hx, inv_one, one_mul, one_mul]
  · rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
      (C.isMu0 i).triv.1, hδ.triv.1, C.isEta.res.1, Formalism.L2.Host.etaFin, GlobalTheory.ClassScalarValue.above_eq,
      Finset.card_pair hQ.symm, ite_eq_right (by norm_num), inv_one, one_mul, one_mul]
  · change (C.mu0 i).loc Q x * (C.delAt l).loc Q x * ((C.eta.loc Q x)⁻¹) = 1
    rw [(C.isMu0 i).tame Q x hx hx',
      hδ.tame Q x hx hx', C.isEta.unr Q x hx, inv_one, one_mul, one_mul]



theorem twisted_kernel_char : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ (ψ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) (I : Type) (_ : Fintype I) (φs : I → D.host.E →+* ℂ) (n : I → ℤ), b ≠ 0 ∧ (∀ Q ∈ Ps, (b : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ChrEq (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ψ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) ∧ (∀ Q, ψ.TameAt Q) ∧ ψ.HasInf φs n := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i _ v _ _ _ _ _ _ _ _ ℓ _ _ χ ξR ω φ hK Λ h N _ _ _ _ _ e Ps yd _ _ hb
  obtain ⟨b, n, h0, h1, h2, h3, h4, h5⟩ := frame_char D R.C i (Formalism.EigenvalueLevelCeiling.plc v)
  refine ⟨_, b, _, _, _, n, h0, fun Q hQ hm => hb Q hQ ?_,
    GlobalTheory.ClassScalarValue.chrEq_mul_inv (hC.lev.mu0 i) hK.chr hC.lev.eta, h2, h3, h4, h5⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (h1 Q hm)

end GlobalTheory.TwistedKernelChar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelCharacterIsTameHeckeUnramifiedStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.twistedKernelCharacter_isTameHecke_unramified : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ (ψ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) (I : Type) (_ : Fintype I) (φs : I → D.host.E →+* ℂ) (n : I → ℤ), b ≠ 0 ∧ (∀ Q ∈ Ps, (b : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ChrEq (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ψ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) ∧ (∀ Q, ψ.TameAt Q) ∧ ψ.HasInf φs n := by
  first | exact @GlobalTheory.TwistedKernelChar.twisted_kernel_char | exact GlobalTheory.TwistedKernelChar.twisted_kernel_char | (intros; apply GlobalTheory.TwistedKernelChar.twisted_kernel_char <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegral

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.ClassScalarIntegral



theorem class_scalar_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∀ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) → ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * a) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM hLN hΛ e Ps yd hh he hPs hs hy hcard a ha lam hTl
  have lemL1 := GlobalTheory.T.exists_coprime_mul_inv_genusLatticeScalar_integral
  have lemHV := GlobalTheory.T.exists_isIntegral_absNorm_pow_mul_onId_of_coprime
  have lemCC := GlobalTheory.T.exists_detIdeal_coprime_splitSupportedPoint
  have lemPSI := GlobalTheory.T.twistedKernelCharacter_isTameHecke_unramified
  obtain ⟨ψ, b, I, _, φs, n, hb0, hbP, hc, hu, hr, htame, hinf⟩ :=
    lemPSI D G Pl0 T0 A T R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM
      hLN hΛ e Ps yd hh he hPs
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime lam
  obtain ⟨cc, c0, cb, cl, cv⟩ := lemCC D (Vc D i) hO.2.lift.std.1 hO.2.lift.std.2 h e Ps yd he hs hy b hbP _ ψ hc hu hr Λ hΛ
    (Formalism.EigenvalueLevelCeiling.plc lam) hp hTl
  obtain ⟨K, hK1⟩ := lemHV D.host.E ψ I φs n hinf htame b hb0 hu cc c0 cb
  obtain ⟨m, hm, hm1⟩ := lemL1 D T hT ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ Λ (O i).s0 (Formalism.EigenvalueLevelCeiling.plc lam) hp hU hTb hTl
  refine ⟨((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL), ?_, ?_⟩
  · intro hmem
    have hco : Nat.Coprime (m * Ideal.absNorm cc ^ K) (Formalism.EigenvalueLevelCeiling.plc lam) := Nat.Coprime.mul_left hm (Nat.Coprime.pow_left _ cl)
    have h1 : ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) ∈ lam.asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem lam
    obtain ⟨u, w, huw⟩ : IsCoprime ((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL) ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) :=
      Nat.Coprime.cast hco
    exact lam.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (huw ▸ lam.asIdeal.add_mem (lam.asIdeal.mul_mem_left _ hmem) (lam.asIdeal.mul_mem_left _ h1)))
  · have hinj : Function.Injective D.what₂.embLL.toIntAlgHom := D.what₂.embLL.injective
    refine (isIntegral_algHom_iff _ hinj).1 ?_
    have e1 : D.what₂.embLL.toIntAlgHom (((((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL)) : D.what₂.LL) * a) =
        ((m : ℂ) * ((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹) *
        (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ)) *
        ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℝ) : ℂ) := by
      rw [RingHom.toIntAlgHom_apply, map_mul, ha, ← cv]
      push_cast
      rw [map_mul, map_pow, map_natCast, map_natCast]
      ring
    rw [e1]
    refine (hm1.mul hK1).mul ?_
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), ← Nat.cast_pow, Complex.ofReal_natCast]
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ D.R.r : ℕ) : ℤ)))

end GlobalTheory.ClassScalarIntegral
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegralStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.twisted_kernel_class_scalar_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∀ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) → ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * a) := by
  first | exact @GlobalTheory.ClassScalarIntegral.class_scalar_integral | exact GlobalTheory.ClassScalarIntegral.class_scalar_integral | (intros; apply GlobalTheory.ClassScalarIntegral.class_scalar_integral <;> assumption)
end
end
