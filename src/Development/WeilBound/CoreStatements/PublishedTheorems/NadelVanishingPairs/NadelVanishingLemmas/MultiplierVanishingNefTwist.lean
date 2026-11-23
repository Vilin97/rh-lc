module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleAddNefIsAmple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorOfForm
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncBoundaryAmpleDecomposition
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AmpleAddNefIsAmple

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.ample_add_nef_is_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (A N P : LB X) (hA : IsAmpleLB A) (hN : letI := algebraΓOfHom p; IsNef k N) (hP : P.IsLB), cls P hP = cls A hA.isLB + cls N (letI := algebraΓOfHom p; hN.isLB) → IsAmpleLB P := by
  first | exact @_root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef | exact _root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef | (intros; apply _root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultipleBelowThreshold

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoefBound

theorem cartierDivisor_mult_nsmul_eq_natCast_mul {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X)
    (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    have h := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h
    rw [zero_nsmul]; push_cast; omega
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem coef_lt_of_large : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] (R Fd : CartierDiv Y) (m r a : ℕ), 0 < r → (∀ z, R.mult z < m) → ∃ b : ℕ, a ≤ b ∧ ∀ z, ((r * b) • R + m • Fd).mult z < (m * r * b : ℕ) := by
  intro Y _ _ _ R Fd m r a hr hR
  classical
  have hfin := Fd.finite_support_mult
  set S : ℕ := ∑ z ∈ hfin.toFinset, ((m : ℤ) * Fd.mult z).toNat with hS
  refine ⟨a + 1 + S, by omega, fun z => ?_⟩
  have hF : (m : ℤ) * Fd.mult z < ((a + 1 + S : ℕ) : ℤ) := by
    by_cases hz : Fd.mult z = 0
    · rw [hz]; push_cast; omega
    · have hmem : z ∈ hfin.toFinset := by simpa using hz
      have h1 : ((m : ℤ) * Fd.mult z).toNat ≤ S :=
        Finset.single_le_sum (f := fun z => ((m : ℤ) * Fd.mult z).toNat) (fun _ _ => Nat.zero_le _) hmem
      have h2 : (m : ℤ) * Fd.mult z ≤ (((m : ℤ) * Fd.mult z).toNat : ℤ) := Int.self_le_toNat _
      have h3 : ((((m : ℤ) * Fd.mult z).toNat : ℕ) : ℤ) ≤ (S : ℤ) := by exact_mod_cast h1
      push_cast; omega
  rw [CartierDiv.mult_add, cartierDivisor_mult_nsmul_eq_natCast_mul, cartierDivisor_mult_nsmul_eq_natCast_mul]
  set b : ℕ := a + 1 + S
  have hRz : R.mult z ≤ (m : ℤ) - 1 := by have := hR z; omega
  have hrb : (0 : ℤ) ≤ ((r * b : ℕ) : ℤ) := by positivity
  have key : ((r * b : ℕ) : ℤ) * R.mult z ≤ ((r * b : ℕ) : ℤ) * ((m : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left hRz hrb
  have hb : ((b : ℕ) : ℤ) ≤ ((r * b : ℕ) : ℤ) := by
    have : b ≤ r * b := Nat.le_mul_of_pos_left b hr
    exact_mod_cast this
  have e : (((m * r * b : ℕ)) : ℤ) = ((r * b : ℕ) : ℤ) * (m : ℤ) := by push_cast; ring
  rw [e]
  nlinarith

end GlobalTheory.CoefBound
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsMultipleBelowThreshold

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_multiple_below_threshold : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] (R Fd : CartierDiv Y) (m r a : ℕ), 0 < r → (∀ z, R.mult z < m) → ∃ b : ℕ, a ≤ b ∧ ∀ z, ((r * b) • R + m • Fd).mult z < (m * r * b : ℕ) := by
  first | exact @_root_.GlobalTheory.CoefBound.coef_lt_of_large | exact _root_.GlobalTheory.CoefBound.coef_lt_of_large | (intros; apply _root_.GlobalTheory.CoefBound.coef_lt_of_large <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefPullbackIsNef

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NumPull

theorem isNef_pull_of_isProjOver : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (s : Y ⟶ X), IsProjOver p → ∀ N : LB X, (letI := algebraΓOfHom p; IsNef k N) → (letI := algebraΓOfHom (s ≫ p); IsNef k (N.pull s)) := by
  intro k _ X Y p s hp N hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (s ≫ p)
  have : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  refine ⟨pull_isLB hN.isLB s, fun C hC => ?_⟩
  rcases interNumRed_pull_curve p s C hC with h | ⟨C', hC', d, hd⟩
  · rw [h N hN.isLB]
  · rw [hd N hN.isLB]
    exact mul_nonneg (Int.natCast_nonneg d) (hN.nonneg C' hC')

end GlobalTheory.NumPull
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NefPullbackIsNef

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.nef_pullback_is_nef : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (s : Y ⟶ X), IsProjOver p → ∀ N : LB X, (letI := algebraΓOfHom p; IsNef k N) → (letI := algebraΓOfHom (s ≫ p); IsNef k (N.pull s)) := by
  first | exact @_root_.GlobalTheory.NumPull.isNef_pull_of_isProjOver | exact _root_.GlobalTheory.NumPull.isNef_pull_of_isProjOver | (intros; apply _root_.GlobalTheory.NumPull.isNef_pull_of_isProjOver <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncBoundaryAmpleDecompositionStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.snc_boundary_ample_decomposition : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (Kc : CanonLB q n) (Q A : LB Y) (hQ : Q.IsLB) (hA : IsAmpleLB A) (B : Closeds Y) (Γ : CartierDiv Y) (e : ℕ), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → Γ.Eff → Γ.supp ≤ B → (∀ z, Γ.mult z < e) → e • cls Q hQ = e • cls Kc.bundle Kc.isLB + toPic Γ + cls A hA.isLB → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  first | exact @_root_.GlobalTheory.Div.SncBoundary.vanishing_ample_snc_cartier | exact _root_.GlobalTheory.Div.SncBoundary.vanishing_ample_snc_cartier | (intros; apply _root_.GlobalTheory.Div.SncBoundary.vanishing_ample_snc_cartier <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwist

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogResVanish

open GlobalTheory.Cartier.CartierDiv in
private theorem mult_zero₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y) :
    (0 : CartierDiv Y).mult z = 0 := by
  have h := CartierDiv.mult_add (0 : CartierDiv Y) 0 z
  rw [add_zero] at h
  linarith

private theorem mult_nsmul₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (D : CartierDiv Y) (n : ℕ) (z : Y) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero => rw [zero_nsmul, mult_zero₀]; simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

private theorem mult_sub₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (D E : CartierDiv Y) (z : Y) : (D - E).mult z = D.mult z - E.mult z := by
  have h := CartierDiv.mult_add (D - E) E z
  rw [sub_add_cancel] at h
  linarith

private theorem eff_nsmul {Y : Scheme.{0}} [IsIntegral Y] {D : CartierDiv Y} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

private theorem supp_nsmul_le {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) (n : ℕ) :
    (n • D).supp ≤ D.supp := by
  induction n with
  | zero => rw [zero_nsmul, (CartierDiv.supp_eq_bot_iff).2 rfl]; exact bot_le
  | succ n ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

private theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

end GlobalTheory.LogResVanish


open GlobalTheory.LogResVanish in
theorem GlobalTheory.Discrepancy.vanishing_logRes_floor : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → ∀ (Q : LB Y) (hQ : Q.IsLB), cls Q hQ = CechPic.pull s (cls N hN) - toPic F → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B F hη hm h hF N M T hN hM r hT hr hTc hMn a Fd A hA hAF Q hQ hQc i hi
  obtain ⟨ha, hFd, hFdB, hAc⟩ := hAF
  have hTlb : T.IsLB := by letI := algebraΓOfHom p; exact hT.isLB
  haveI := h.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.isNormalScheme_of_smooth (s ≫ p)
  haveI : CompactSpace Y := compactSpace_of_projOver h.proj
  haveI : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'

  set Γ := pullCart s G - m • K with hΓ
  set R := Γ - m • F with hR
  have hRm : ∀ z, R.mult z = Γ.mult z % (m : ℤ) := fun z => by
    rw [hR, mult_sub₀, mult_nsmul₀, hF z, Int.emod_def]
  have hR0 : ∀ z, 0 ≤ R.mult z := fun z => (hRm z).symm ▸ Int.emod_nonneg _ hm0
  have hRlt : ∀ z, R.mult z < m := fun z =>
    (hRm z).symm ▸ Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  have hReff : R.Eff := ((GlobalTheory.T.cartier_divisor_mult_characterize Y R).1).2 hR0
  have hRB : R.supp ≤ B := fun x hx => by
    obtain ⟨z, hzx, hz⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y R).2.1 x).1 hx
    refine h.supp (((GlobalTheory.T.cartier_divisor_mult_characterize Y Γ).2.1 x).2 ⟨z, hzx, fun e => hz ?_⟩)
    rw [hRm, e, Int.zero_emod]

  obtain ⟨b, hab, hb⟩ := GlobalTheory.T.exists_multiple_below_threshold Y R Fd m r a hr hRlt
  set Γ' := (r * b) • R + m • Fd with hΓ'
  have hΓ'eff : Γ'.Eff := (eff_nsmul hReff _).add (eff_nsmul hFd _)
  have hΓ'B : Γ'.supp ≤ B := (CartierDiv.supp_add_le _ _).trans
    (sup_le ((supp_nsmul_le _ _).trans hRB) ((supp_nsmul_le _ _).trans hFdB))

  have hAm : IsAmpleLB (lbPow A m) := (isAmpleLB_pow_iff hA.isLB hm).2 hA
  letI := algebraΓOfHom (s ≫ p)
  have hTp : IsNef k (T.pull s) := GlobalTheory.T.nef_pullback_is_nef k X Y p s hp T hT
  have hMp : IsNef k (M.pull s) := GlobalTheory.T.nef_pullback_is_nef k X Y p s hp M hMn
  obtain ⟨P, hP, hPc⟩ := cls_surj (b • cls (T.pull s) hTp.isLB + (m * (b - a)) • cls (M.pull s) hMp.isLB)
  have hPn : IsNef k P := (hTp.pow hA b).of_cls_eq_add (hMp.pow hA (m * (b - a))) hA hP
    (by rw [hPc, cls_lbPow hTp.isLB, cls_lbPow hMp.isLB])
  obtain ⟨A', hA'lb, hA'c⟩ := cls_surj (cls (lbPow A m) hAm.isLB + cls P hPn.isLB)
  have hA' : IsAmpleLB A' := GlobalTheory.T.ample_add_nef_is_ample k Y (s ≫ p) h.proj (lbPow A m) P A' hAm hPn hA'lb hA'c

  let Kc := CanonLB.all (s ≫ p) n
  have hne : EtaleKlt.ratPull p s n η ≠ 0 := fun e =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p s h.bir n).1 (e.trans (map_zero _).symm))
  have hK : toPic K = cls Kc.bundle Kc.isLB := (GlobalTheory.T.canonical_divisor_of_form k Y (s ≫ p) n _ hne).2 K h.div Kc
  refine GlobalTheory.T.snc_boundary_ample_decomposition k Y (s ≫ p) n h.proj Kc Q A' hQ hA' B Γ' (m * r * b) h.snc hΓ'eff hΓ'B hb ?_ i hi

  rw [hA'c, cls_lbPow hA.isLB, hPc, cls_pull hTlb, cls_pull hM, hTc, ← hK, hQc]
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  have e1 : toPic Γ' = (r * (a + c)) • (toPic (pullCart s G) - m • toPic K - m • toPic F) +
      m • toPic Fd := by
    rw [hΓ', hR, hΓ]; simp only [map_add (f := _), map_nsmul, map_sub]
  have e2 : m • toPic Fd = m • (a • CechPic.pull s (cls M hM) - cls A hA.isLB) := by
    rw [hAc, add_sub_cancel_left]
  rw [e1, add_assoc, e2, toPic_pullCart]
  simp only [map_sub, map_nsmul, Nat.add_sub_cancel_left]
  module
end
end
