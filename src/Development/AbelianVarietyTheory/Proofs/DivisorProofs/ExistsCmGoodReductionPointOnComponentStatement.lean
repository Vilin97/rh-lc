module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmExistsHolds
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFramedPointOfLieEigenbasisStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamLettersIsGood
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamObjGoodOfCmObj
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsEigenvectorAtOfModelStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LeftEqOfIsLieCombSingle
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullbackStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SabMapCancelAndCompOver
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataNonemptyField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLatticeDataOfAdaptedBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InvMulVecEqZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalLatticeFrameFlagDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmLatticeDataUnfoldingSignatureOneZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.CMRankOne

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_pure_of_data (Y : FD.Data E r) (x : FD.Frame Y.Ψ r) (hx : x ∈ Y.dom) (lam : Fin r → Fin r → E)
    (ho : ∀ j k' : Fin r, (j : ℕ) < Y.p0 → Y.p0 ≤ (k' : ℕ) → FD.herm Y.Gm (lam j) (lam k') = 0)
    (hsp : ∀ τ : Y.Ψ, Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.col (FD.mat x τ) (Fin.castLE Y.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.Data.emb τ.1 (lam (Fin.castLE Y.p0_le a))))
    (a : E) (j : Fin r) (τ : E →+* ℂ) (i : ℕ) :
    ((j : ℕ) < Y.p0 → τ ∈ Y.Ψ → perFr Y x (a • lam j) τ i = 0) ∧
      (Y.p0 ≤ (j : ℕ) → τ ∉ Y.Ψ → i < Y.p0 → perFr Y x (a • lam j) τ i = 0) := by
  refine ⟨fun hj hτ => ?_, fun hj hτ hi => ?_⟩
  · unfold perFr
    rw [dite_eq_left hτ]
    split_ifs with h
    · refine GlobalTheory.PurePer.inv_mulVec_eq_zero Y.p0_le _ (hx ⟨τ, hτ⟩).1 ?_ _ (by simp)
      rw [hsp ⟨τ, hτ⟩, GlobalTheory.PurePer.emb_smul']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · rfl
  · unfold perFr
    rw [dite_eq_right hτ]
    split_ifs with h' h
    · have hm : FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨Y.p0 - 1 - i, h⟩ ∈
          Submodule.span ℂ (Set.range fun a : Fin Y.p0 =>
            FD.Data.emb (conjEmb τ) (lam (Fin.castLE Y.p0_le a))) := by
        have := hsp ⟨conjEmb τ, h'⟩
        simp only at this
        rw [← this]
        exact Submodule.subset_span ⟨⟨Y.p0 - 1 - i, by omega⟩, rfl⟩
      rw [GlobalTheory.PurePer.emb_smul', FD.hermC_smul_right]
      refine mul_eq_zero_of_right _ ?_
      generalize FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨Y.p0 - 1 - i, h⟩ = w at hm
      induction hm using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨k, rfl⟩ := hw
        rw [FD.hermC_emb, ho _ j (by simpa using k.isLt) hj, map_zero]
      | zero => exact FD.hermC_zero_left _ _ _
      | add a b _ _ ha hb => rw [FD.hermC_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [FD.hermC_smul_left, ha, mul_zero]
    · rfl
    · rfl

theorem exists_cmLat_rankOne (H : Host E) {p q : ℕ} (Y : FD.Data E r) (x₀ : Y.dom)
    (hr : 0 < r) (hrk : r = p + q) (hp0 : Y.p0 = q) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0)
    (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (φ : D.La ≃ₗ[𝓞 E] Y.Λ)
    (isom : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-Y.ξ0 * FD.herm Y.Gm (φ a : Fin r → E) (φ b)))
    (ix : Fin g → ℕ) (hix : ∀ j, ty j (H.rt : E) ≠ H.rt0 → ix j < q)
    (pm : ∀ a j, Pe a j = perFr Y x₀.1 (φ a : Fin r → E) (ty j) (ix j))
    (D₁ : Datum H) (hp1 : D₁.p = 1) (hq1 : D₁.q = 0)
    (lam : Fin r → Fin r → E) (hL : ∀ j, lam j ∈ Y.Λ) (hli : LinearIndependent E lam)
    (ho : ∀ j k' : Fin r, (j : ℕ) < Y.p0 → Y.p0 ≤ (k' : ℕ) → FD.herm Y.Gm (lam j) (lam k') = 0)
    (hsp : ∀ τ : Y.Ψ, Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.col (FD.mat x₀.1 τ) (Fin.castLE Y.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.Data.emb τ.1 (lam (Fin.castLE Y.p0_le a)))) :
    Nonempty (CMLat hP p q) := by
  classical
  have hpure := perFr_pure_of_data Y x₀.1 x₀.2 lam ho hsp
  obtain ⟨G1, io, hioinj, -, -, hG1det, hEF1⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H D₁ Y.ξ0 Y.ξ0_im Y.ξ0_ne 1 (by omega)
  let lv : D₁.La →ₗ[𝓞 E] E := (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 1 => E) 0) ∘ₗ io
  have hlv : ∀ x, lv x = io x 0 := fun x => rfl
  have hG0 : G1 0 0 ≠ 0 := by simpa [Matrix.det_unique] using hG1det
  have hform1 : ∀ x y, ((D₁.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (Y.ξ0 * G1 0 0 * lv x * FD.cc (lv y)) := by
    intro x y
    rw [hEF1]
    congr 1
    simp [FD.herm, hlv]
    ring
  have h1ne : (1 : Submodule (𝓞 E) E) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨1, Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero⟩

  obtain ⟨S, hS⟩ := D₁.fin.fg_top
  obtain ⟨N₀, hN₀, hc₀⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (1 : Submodule (𝓞 E) E) h1ne (fun s : S => lv s)
  let lv0 : D₁.La →ₗ[𝓞 E] E := (N₀ : 𝓞 E) • lv
  have hlv0 : ∀ x, lv0 x = (N₀ : E) * lv x := fun x => by
    simp [lv0, Algebra.smul_def]
  have hlv01 : ∀ x, lv0 x ∈ (1 : Submodule (𝓞 E) E) := by
    have : (⊤ : Submodule (𝓞 E) D₁.La) ≤ (1 : Submodule (𝓞 E) E).comap lv0 := by
      rw [← hS, Submodule.span_le]
      intro s hs
      change lv0 s ∈ (1 : Submodule (𝓞 E) E)
      rw [hlv0]
      exact hc₀ ⟨s, hs⟩
    exact fun x => this Submodule.mem_top

  obtain ⟨M, hM, hcM⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (1 : Submodule (𝓞 E) E) h1ne
    (fun i : Fin r => (N₀ : E) ^ 2 * FD.herm Y.Gm (lam i) (lam i) / G1 0 0)
  choose t ht using fun i => Submodule.mem_one.1 (hcM i)
  let lv' : D₁.La →ₗ[𝓞 E] E := (M : 𝓞 E) • lv0
  have hlv' : ∀ x, lv' x = ((N₀ * M : ℕ) : E) * lv x := fun x => by
    simp only [lv', LinearMap.smul_apply, Algebra.smul_def, hlv0]
    push_cast
    ring
  have hlv'1 : ∀ x, lv' x ∈ (1 : Submodule (𝓞 E) E) := fun x =>
    Submodule.smul_mem _ (M : 𝓞 E) (hlv01 x)
  have hmem : ∀ x j, lv' x • lam j ∈ Y.Λ := fun x j => by
    obtain ⟨u, hu⟩ := Submodule.mem_one.1 (hlv'1 x)
    rw [← hu, algebraMap_smul]
    exact Y.Λ.smul_mem u (hL j)
  let m : Fin r → D₁.La →ₗ[𝓞 E] Y.Λ := fun j =>
    { toFun := fun a => ⟨_, hmem a j⟩
      map_add' := fun a b => Subtype.ext (by simp [add_smul])
      map_smul' := fun c a => Subtype.ext (by simp [smul_assoc]) }
  let Dp : Bool → Datum H := fun b => match b with
    | true => D₁
    | false => oppDatum D₁
  let e : ∀ b, (Dp b).La ≃ₗ[𝓞 E] D₁.La := fun b => match b with
    | true => LinearEquiv.refl _ _
    | false => LinearEquiv.refl _ _
  let σ : Fin p ⊕ Fin q ≃ Fin r := (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσl : ∀ j, q ≤ (σ (.inl j) : ℕ) := fun j => by simp [σ]
  have hσr : ∀ j, (σ (.inr j) : ℕ) < q := fun j => by simp [σ]
  let f : ∀ j : Fin p ⊕ Fin q, (Dp j.isLeft).La →ₗ[𝓞 E] D.La := fun j =>
    φ.symm.toLinearMap ∘ₗ m (σ j) ∘ₗ (e _).toLinearMap
  have hf : ∀ j a, (φ (f j a) : Fin r → E) = lv' (e _ a) • lam (σ j) := fun j a => by
    simp [f, m]
  let hh : Fin p ⊕ Fin q → 𝓞 E :=
    Sum.elim (fun j => -((M : 𝓞 E) * t (σ (.inl j)))) (fun j => (M : 𝓞 E) * t (σ (.inr j)))
  have hhl : ∀ j, ((hh (.inl j) : 𝓞 E) : E) =
      -(((N₀ * M : ℕ) : E) ^ 2 * FD.herm Y.Gm (lam (σ (.inl j))) (lam (σ (.inl j))) / G1 0 0) := by
    intro j
    show ((-((M : 𝓞 E) * t (σ (.inl j))) : 𝓞 E) : E) = _
    rw [RingOfIntegers.coe_eq_algebraMap, map_neg, map_mul, ht, map_natCast]
    push_cast
    ring
  have hhr : ∀ j, ((hh (.inr j) : 𝓞 E) : E) =
      ((N₀ * M : ℕ) : E) ^ 2 * FD.herm Y.Gm (lam (σ (.inr j))) (lam (σ (.inr j))) / G1 0 0 := by
    intro j
    show ((((M : 𝓞 E) * t (σ (.inr j))) : 𝓞 E) : E) = _
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, ht, map_natCast]
    push_cast
    ring
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := fun τ => by
    refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  have h3 : ∀ (a b : E) (u : Fin r → E), FD.herm Y.Gm (a • u) (b • u) = a * FD.cc b * FD.herm Y.Gm u u :=
    fun a b u => by
      simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hccN : ∀ n : ℕ, FD.cc (n : E) = n := fun n => by simp [FD.cc]
  have hlvs : ∀ (c : 𝓞 E) x, lv (c • x) = (c : E) * lv x := fun c x => by
    rw [map_smul, Algebra.smul_def]
  refine ⟨⟨Dp, ⟨hp1, hq1⟩, ⟨hq1, hp1⟩, f, ?_, hh, ?_, ?_⟩⟩
  · rintro (j | j) a k hk
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).2 (hp0 ▸ hσl j) (fun h => hk' ((hΨ _).1 h)) (hp0 ▸ hix k hk')
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ -H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).1 (hp0 ▸ hσr j) ((hΨ _).2 ((hsq _).resolve_right hk'))
  · rintro (j | j) a b
    · apply Int.cast_injective (α := ℚ)
      rw [isom, hf, hf]
      refine Eq.trans ?_ (hform1 (hh (.inl j) • a) b).symm
      erw [hlvs]
      congr 1
      change -Y.ξ0 * FD.herm Y.Gm (lv' a • lam (σ (.inl j))) (lv' b • lam (σ (.inl j))) = _
      rw [h3]
      erw [hlv' a, hlv' b]
      rw [hhl]
      simp only [FD.cc, map_mul, map_natCast]
      field_simp
    · apply Int.cast_injective (α := ℚ)
      rw [isom, hf, hf]
      refine Eq.trans ?_ (congrArg (fun z : ℚ => -z) (hform1 (hh (.inr j) • a) b)).symm |>.trans (by push_cast; rfl)
      erw [hlvs]
      rw [← map_neg]
      congr 1
      change -Y.ξ0 * FD.herm Y.Gm (lv' a • lam (σ (.inr j))) (lv' b • lam (σ (.inr j))) = _
      rw [h3]
      erw [hlv' a, hlv' b]
      rw [hhr]
      simp only [FD.cc, map_mul, map_natCast]
      field_simp
  · haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    have hB : ∀ j, B j = lam j := fun j => by simp [B]
    let Nm : Submodule (𝓞 E) D.La := LinearMap.range (∑ j, f j ∘ₗ LinearMap.proj j)
    have hN : ∀ a, a ∈ Nm ↔ ∃ x : ∀ j : Fin p ⊕ Fin q, (Dp j.isLeft).La, a = ∑ j, f j (x j) := fun a => by
      simp only [Nm, LinearMap.mem_range, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact exists_congr fun _ => eq_comm
    have hnt : Nontrivial D₁.La :=
      Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D₁.rank, hp1, hq1]; exact one_pos)
    obtain ⟨a₀, ha₀⟩ := exists_ne (0 : D₁.La)
    have hR : LinearMap.range lv' ≠ ⊥ := by
      refine (Submodule.ne_bot_iff _).2 ⟨lv' a₀, ⟨a₀, rfl⟩, ?_⟩
      rw [hlv']
      refine mul_ne_zero (by exact_mod_cast (Nat.mul_pos hN₀ hM).ne') fun h0 => ha₀ (hioinj ?_)
      funext i
      rw [Subsingleton.elim i 0, map_zero]
      exact h0
    obtain ⟨S', hS'⟩ := D.fin.fg_top
    obtain ⟨n, hn, hc⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (LinearMap.range lv') hR
      (fun i : S' × Fin r => B.repr (φ i.1 : Fin r → E) i.2)
    choose y hy using fun i : S' × Fin r => LinearMap.mem_range.1 (hc i)
    refine ⟨n, hn, fun a => (hN _).1 ?_⟩
    have : (⊤ : Submodule (𝓞 E) D.La) ≤ Nm.comap (n • LinearMap.id) := by
      rw [← hS', Submodule.span_le]
      intro a ha
      refine (hN _).2 ⟨fun j => (e _).symm (y (⟨a, ha⟩, σ j)), φ.injective (Subtype.ext ?_)⟩

      rw [map_sum, AddSubmonoidClass.coe_finsetSum]
      simp only [hf, LinearEquiv.apply_symm_apply, hy]
      rw [Equiv.sum_comp σ (fun j => ((n : E) * B.repr (φ a : Fin r → E) j) • lam j)]
      simp only [mul_smul, ← Finset.smul_sum, ← hB, B.sum_repr]
      simp [Nat.cast_smul_eq_nsmul]
    exact this Submodule.mem_top

theorem exists_cmLat_unfAt_rankOne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (r : ℕ) (U : Formalism.L2.Pj.Unf Xo c c.F.val.toRingHom r), Formalism.L2.Pj.IsUnf U → 0 < r → ∀ (D₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), D₁.p = 1 → D₁.q = 0 → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k x₀) (lam : Fin r → Fin r → E), (∀ j, lam j ∈ (U.X k).Λ) → LinearIndependent E lam → (∀ j k' : Fin r, (j : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (k' : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam k') = 0) → (∀ j : Fin r, (j : ℕ) < (U.X k).p0 → ∀ τ : (U.X k).Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re) → (∀ j : Fin r, (U.X k).p0 ≤ (j : ℕ) → ∀ τ : (U.X k).Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re < 0) → (∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀.1 τ) (Fin.castLE (U.X k).p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE (U.X k).p0_le a)))) → Nonempty (GlobalTheory.CM.CMLat W.per Dw.p Dw.q) := by
  intro E _ _ _ H Dw l Xo c r U hU hr D₁ hp1 hq1 k x₀ W lam hL hli ho _ _ hsp
  obtain ⟨h1, h2, -⟩ := hU
  refine exists_cmLat_rankOne H (U.X k) x₀ hr h1 (h2 k).1 (h2 k).2 _ W.per (W.φ k) (W.isom k)
    (fun j => (W.e j).2) (fun j hj => ?_) W.pm_eq D₁ hp1 hq1 lam hL hli ho hsp
  exact (W.e j).2.2.trans_eq (if_neg hj)

end GlobalTheory.LamT.CMRankOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmLatticeDataUnfoldingSignatureOneZeroStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.exists_cmLattice_data_unfolding_signature_one_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (r : ℕ) (U : Formalism.L2.Pj.Unf Xo c c.F.val.toRingHom r), Formalism.L2.Pj.IsUnf U → 0 < r → ∀ (D₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), D₁.p = 1 → D₁.q = 0 → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k x₀) (lam : Fin r → Fin r → E), (∀ j, lam j ∈ (U.X k).Λ) → LinearIndependent E lam → (∀ j k' : Fin r, (j : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (k' : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam k') = 0) → (∀ j : Fin r, (j : ℕ) < (U.X k).p0 → ∀ τ : (U.X k).Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re) → (∀ j : Fin r, (U.X k).p0 ≤ (j : ℕ) → ∀ τ : (U.X k).Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re < 0) → (∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀.1 τ) (Fin.castLE (U.X k).p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE (U.X k).p0_le a)))) → Nonempty (GlobalTheory.CM.CMLat W.per Dw.p Dw.q) := by
  first | exact @GlobalTheory.LamT.CMRankOne.exists_cmLat_unfAt_rankOne | exact GlobalTheory.LamT.CMRankOne.exists_cmLat_unfAt_rankOne | (intros; apply GlobalTheory.LamT.CMRankOne.exists_cmLat_unfAt_rankOne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmGoodReductionPointOnComponent

section

@[expose] public section

namespace GlobalTheory.FlatCore.CMPointExistence

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT



theorem exists_frPt_of_cmObj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ : K →+* ℂ) (X : CMObj H K ρ σ Dw.p Dw.q) (La : ℝ) (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (_ : SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K) K))), (∀ τ, τ ∈ LamF.psiSet H ↔ LamF.labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → x ≫ Xo.s = sOf c K → ∃ y : FrPt Xo c K, y.x = x := by
  intro E _ _ _ H Dw l Xo c _ hstar K _ _ _ ρ σ X La x Φ m' hρ hLa hx
  have hfib : LamF.IsFibreOf X.B.pol Φ.key (LamF.gmap K) m'.φ :=
    (LamF.isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) X.B.pol Φ.key m'.φ).2
      ((GlobalTheory.T.principalTriple_pullback E H (𝓞 K) K (algebraMap (𝓞 K) K) X.B).2 Φ.T m' inferInstance).2.1
  obtain ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, -, -, hgood⟩ :=
    LamF.exists_lamObjGood_of_cmObj GlobalTheory.firstFiveLaws.2.1.secTwist GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H l c hstar K ρ σ Dw.p Dw.q X La hρ hLa Φ.key m'.φ hfib
  obtain ⟨L, hL, hm⟩ := LamF.exists_lamLetters_isGood E H l c _ _ _ _ La hgood
  have hdet := LamF.Ind.lamInd E H l c hstar _ _ _ _ La hgood L hL
  have heig := LamF.LetterEigen.letter_eigen E H l c _ _ _ _ La hgood L hL
  obtain ⟨mm, e, src, U, ℓ⟩ := L
  have hmm : mm = Dw.mult := by
    funext b
    unfold Datum.mult
    split_ifs with h
    · exact (hm b).1 h
    · exact (hm b).2 h
  subst hmm
  choose w hw hU using hL.2.2.1
  obtain ⟨y, hy, -, -⟩ := GlobalTheory.T.exists_framedPoint_of_lie_eigenbasis E H Dw l Xo c K x Φ e U w hx hdet hU (fun τ i =>
    GlobalTheory.T.isEigenvectorAt_of_model E H Dw l Xo c K x Φ.T.t X.B.t Φ.m m' τ (w (e ⟨τ, i⟩)) (fun a => by
      have h := heig τ i (w (e ⟨τ, i⟩)) (hw _) a
      rw [← hoa]
      exact h))
  exact ⟨y, hy⟩

end GlobalTheory.FlatCore.CMPointExistence

namespace GlobalTheory.FlatCore

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore



theorem exists_cmPt_on_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (y : FrPt Xo c K) (ρ₀ : 𝓞 K) (σ₁ : K →+* ℂ) (X : GlobalTheory.CM.CMObj H K ρ₀ σ₁ Dw.p Dw.q) (t₀ : SAB H (Sp K)), LiesOn Z y ∧ Nonempty (SABMap t₀ Xo.univ.t y.x) ∧ Nonempty (SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K) K))) ∧ ∀ τ : Psi H, ((ρ₀ : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 H.rt) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z
  let σ₀ : c.F →+* ℂ := c.F.val.toRingHom
  have hσ₀ : GoodEmb c σ₀ := rfl
  obtain ⟨k, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ₀ hσ₀
  have hU := hL.unf σ₀ hσ₀
  have hr : 0 < r := by rw [hU.1]; have := hL.pos; omega
  obtain ⟨D₁, hD₁p, hD₁q⟩ := hL.line
  obtain ⟨x₁, hx₁, lam, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_orthogonal_lattice_frame_flagDomain E r ((U σ₀).X k)
  let x₀ : ((U σ₀).X k).dom := ⟨x₁, hx₁⟩
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hU k x₀
  obtain ⟨Zl⟩ := GlobalTheory.T.exists_cmLattice_data_unfolding_signature_one_zero E H Dw l Xo c r (U σ₀) hU hr D₁ hD₁p hD₁q k x₀ W lam h1 h2 h3 h4 h5 h6
  have hfd : FiniteDimensional ℚ c.F := c.fin
  obtain ⟨K₁, nf, hk1, ρ, X, y, t₀, m, m', -, -, -, -, -, hle, hρ, -, hy, hpt, -⟩ :=
    GlobalTheory.CM.cmExists_holds E H Dw l Xo W.g _ W.F (W.ik k) W.Pm W.per Zl c.F hfd
  letI : Algebra c.F K₁ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  letI : StarRing (𝓞 E) := H.starRing
  obtain ⟨Φ⟩ := GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo K₁ y (by have := hL.pos; omega)
  obtain ⟨n, -⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ Xo.univ.t t₀ Φ.T.t y y (𝟙 _) m Φ.m
    (Category.id_comp _).symm).1
  obtain ⟨mB⟩ : Nonempty (SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K₁) K₁))) := by
    obtain ⟨mm, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabComp ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCubComp E H _ _ _ X.B.t t₀ Φ.T.t _ _ m' n
    rw [Category.id_comp] at mm
    exact ⟨mm⟩
  obtain ⟨yF, hyF⟩ := GlobalTheory.FlatCore.CMPointExistence.exists_frPt_of_cmObj E H Dw l Xo c (fun _ => rfl) K₁ ρ (algebraMap K₁ ℂ) X
    (1 + ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖) y Φ mB
    (fun τ => by
      show τ (H.rt : E) = H.rt0 ↔ _
      rw [← hρ, Subtype.ext_iff]
      exact Iff.rfl) (fun j τ => by
      have h1 : ‖τ (X.hh j : E)‖ ≤ ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖ :=
        calc ‖τ (X.hh j : E)‖ ≤ ∑ τ' : E →+* ℂ, ‖τ' (X.hh j : E)‖ :=
              Finset.single_le_sum (f := fun τ' : E →+* ℂ => ‖τ' (X.hh j : E)‖) (fun _ _ => norm_nonneg _)
                (Finset.mem_univ τ)
          _ ≤ _ := Finset.single_le_sum (f := fun j' => ∑ τ' : E →+* ℂ, ‖τ' (X.hh j' : E)‖)
                (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      have h0 : 0 ≤ ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖ :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      nlinarith) hy
  refine ⟨K₁, inferInstance, nf, inferInstance, yF, ρ, algebraMap K₁ ℂ, X, t₀, ?_, ⟨hyF ▸ m⟩, ⟨m'⟩, fun τ => ?_⟩
  · have hmem : (⟨k, x₁⟩ : Σ k, Frame ((U σ₀).X k).Ψ r) ∈ framesOn (U σ₀) Z := by rw [hk]; exact ⟨rfl, hx₁⟩
    obtain ⟨h', hon⟩ := hmem
    have hpt' : ((U σ₀).un k x₀).x = spMap (algebraMap K₁ ℂ) ≫ yF.x := by rw [hyF, hpt]; exact W.pt
    have key : ptF ((U σ₀).un k x₀) = spMap (algebraMap K₁ ℂ) ≫ ptF yF := by
      apply Limits.pullback.hom_ext
      · unfold ptF
        erw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst]
        exact hpt'
      · unfold ptF
        erw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd]
        erw [← Spec.map_comp]
        rfl
    intro s
    let s' : Sp (CAt σ₀) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have h7 := hon s'
    change ptF ((U σ₀).un k x₀) s' ∈ _ at h7
    rw [key] at h7
    have hs : (spMap (algebraMap K₁ ℂ)) s' = s := Subsingleton.elim (α := PrimeSpectrum K₁) _ _
    rw [← hs]
    exact h7
  · exact Subtype.ext (hρ.trans τ.2.symm)

end GlobalTheory.FlatCore
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmGoodReductionPointOnComponentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.exists_cm_goodReduction_point_on_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (y : FrPt Xo c K) (ρ₀ : 𝓞 K) (σ₁ : K →+* ℂ) (X : GlobalTheory.CM.CMObj H K ρ₀ σ₁ Dw.p Dw.q) (t₀ : SAB H (Sp K)), LiesOn Z y ∧ Nonempty (SABMap t₀ Xo.univ.t y.x) ∧ Nonempty (SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K) K))) ∧ ∀ τ : Psi H, ((ρ₀ : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 H.rt) := by
  first | exact @GlobalTheory.FlatCore.exists_cmPt_on_comp | exact GlobalTheory.FlatCore.exists_cmPt_on_comp | (intros; apply GlobalTheory.FlatCore.exists_cmPt_on_comp <;> assumption)
end
end
