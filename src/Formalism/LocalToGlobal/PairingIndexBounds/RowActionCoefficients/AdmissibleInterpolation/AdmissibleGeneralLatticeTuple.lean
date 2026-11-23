module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.GeXZero
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.CoefficientProductHolds
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HinjX
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.EvalIdFrameRowAct
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HighestVectorFullHolds
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.ShapeEvenHolds
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
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.WeylComplementInDetCoeffSpan
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
public import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.ProdBlockEmbMonomial
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.ShapeEvenHolds
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FockRSmulLeft
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.InterpolationHolds

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.NuTAntitone

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem nuT_antitone (hS : XShape) (j : ℕ) (b : BX X) : Antitone (nuT X j b) := by
  obtain ⟨-, -, hanti, -⟩ := hS p X j b
  unfold nuT
  split_ifs
  · exact BidetPairing.kap_antitone (hanti _) _
  · exact hanti _

theorem shape_szT (hS : XShape) (j : ℕ) (b : BX X) : shapeDeg (szT X j b) = nuT X j b := by
  obtain ⟨-, -, hanti, hle, -⟩ := hS p X j b
  by_cases ho : IsOddPos b.2
  · have h1 : szT X j b = fun k => NJ X (j + 1) - colH (muX X j (NJ X (j + 1)) b) k.val := by
      funext k; exact if_pos ho
    rw [h1, show nuT X j b = _ from if_pos ho]
    exact shape_odd_holds _ _ (hanti _) _ (hle _)
  · have h1 : szT X j b = fun k => colH (muX X j (NJ X (j + 1)) b) k.val := by
      funext k; exact if_neg ho
    rw [h1, show nuT X j b = _ from if_neg ho]
    exact shape_even_holds _ _ (hanti _) _ (hle _)

theorem xPair (hS : XShape) (hBrS : XBrS) (hInj : XInj) (hMid : XMid) (hU : XUnit)
    (Oc : Subring Kc) (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc)
    (hO : ∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc)
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (i0 : X.Pl → ℕ) (h3 : ∀ v, i0 v ≤ X.G.P.r)
    (f : MvPowerSeries (X.ZA j) Kc) (gg : ℝ)
    (hf : ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), geX p Oc (AddMonoidAlgebra.coeff (applyD (X.PI j I i0) f) n) gg)
    (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).HtupW La.2)
    (I : ∀ (b : BX X) (k : Fin (cX X j b)), Fin (szT X j b k) → Fin (NJ X (j + 1))) :
    ∃ a ∈ MG p Oc hval gg,
      fockR ((((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
            ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
              (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) La'.2))⁻¹)) *
            (∏ b : BX X, (mF X (j + 1) b (φ.g' b.1).val * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)))⁻¹) •
          delF X Kc j G (linSub (bc Kc φ) f))
        (map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
          (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1).val * DgX X X.G.Kf j i0 b.1).transpose
            (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b))))) = a * ∏ b, cN Kc (nuT X j b) := by
  classical
  by_cases hI : ∀ b k, Function.Injective (I b k)
  · obtain ⟨Ist, ε, hε, hmid⟩ := hMid p X Kc j La La' φ i0 I hI
    set TI := map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
      (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1).val * DgX X X.G.Kf j i0 b.1).transpose
        (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b)))) with hTI
    set cc : Kc := ∏ b, cN Kc (nuT X j b) with hcc
    have hcc0 : cc ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => cN_ne Kc _
    set S1 : X.G.Kf := ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
            ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
              (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) La'.2))⁻¹)) with hS1
    set s1 : X.G.Kf := (∏ b : BX X, (mF X (j + 1) b (φ.g' b.1).val * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)))⁻¹ with hs1
    have hp0 : (p : Kc) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    have hu := hU p X Kc Oc hO hp0 j La.2 La'.2 φ.g φ.g' φ.hg φ.hg' i0 h3
    rw [← hS1, ← hs1] at hu
    set U0 := numericalIdentityScalar X Kc j (fun v => φ.g v) (fun v => φ.g' v) i0 with hU0
    have hεO : ε ∈ Oc := by
      rcases hε with h | h
      · rw [h]; exact Oc.one_mem
      · rw [h]; exact Oc.neg_mem Oc.one_mem
    have key := phi_mem X Kc hS hBrS hInj j La.2 φ.g φ.hg (MG p Oc hval gg) (fun o a ha => geX_mul (hO o) ha)
      (PhiX X Kc j (fockL TI) (cc⁻¹ * algebraMap X.G.Kf Kc (S1 * s1)) (linSub (bc Kc φ) f))
      (C (ε * (algebraMap X.G.Kf Kc (S1 * sX X j (fun v => φ.g v) * s1) * U0)) * applyD (X.PI j Ist i0) f)
      (fun m => by
        rw [coeff_C_mul]
        exact geX_mul (Oc.mul_mem hεO hu) (hf Ist m))
      (fun x => by
        rw [PhiX_apply, map_smul, LinearMap.smul_apply, ← algebraMap_smul Kc (sX X j fun v => φ.g v), map_smul, smul_eq_mul]
        show _ * (_ * fockR _ TI) = _
        rw [hmid f x]
        simp only [map_mul, eval_C]
        field_simp) G hG
    refine ⟨_, key, ?_⟩
    rw [PhiX_apply, ← algebraMap_smul Kc (S1 * s1), fockR_smul_left]
    show _ = _ * _ * fockR _ TI * cc
    field_simp
  · push Not at hI
    obtain ⟨b0, k0, hk⟩ := hI
    refine ⟨0, AddSubgroup.zero_mem _, ?_⟩
    have hb : bideterminant X.G.Kf (szT X j b0) (szT_le X j b0) (I b0) = 0 := by
      unfold bideterminant
      exact Finset.prod_eq_zero (Finset.mem_univ k0) (minor_zero_holds _ _ _ _ _ _ hk)
    have hz : (∏ b, rename (emX X (j + 1) b)
        (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1).val * DgX X X.G.Kf j i0 b.1).transpose
          (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ b0) (by rw [hb, map_zero, map_zero])
    rw [hz, map_zero, fockR_comm, fockR_zero_left, zero_mul]

end Formalism.L2.PairingIndexBounds.Ent
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.PolyKTorsionFree

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Model

section dual

variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [CharZero K]

lemma toK_eq_map {σ : Type} (f : MvPolynomial σ O) : toK O K f = map (algebraMap O K) f := rfl

lemma polyK_torsionFree {σ : Type} : Module.IsTorsionFree O (MvPolynomial σ K) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun a f h => ?_
  rw [← algebraMap_smul K a f, smul_eq_zero] at h
  rcases h with h | h
  · left; exact (IsFractionRing.injective O K) (by rw [h, map_zero])
  · right; exact h

lemma weylK_fg {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    ((weyl O n n le_rfl ν).map (toK O K)).FG := by
  have hM : ((dualWeyl O n n ν).map (toK O K)).FG := by
    apply Submodule.FG.map
    obtain ⟨b, hb, -⟩ := sSBasis O n n ν
    rw [← hb.2.1]
    have := (sSIdxFinite n n ν).to_subtype
    exact Submodule.fg_span (Set.finite_range b)
  have hle : (weyl O n n le_rfl ν).map (toK O K) ≤ (dualWeyl O n n ν).map (toK O K) :=
    Submodule.map_mono (weylLeDual O n n le_rfl ν hν)
  have := isNoetherian_of_fg_of_noetherian _ hM
  have h := IsNoetherian.noetherian (((weyl O n n le_rfl ν).map (toK O K)).comap
    ((dualWeyl O n n ν).map (toK O K)).subtype)
  have h2 := h.map ((dualWeyl O n n ν).map (toK O K)).subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2

end dual

theorem dual_bases_holds : DualBases := by
  intro O K _ _ _ _ _ _ _ n ν hν
  classical
  set c := fockR (hw K (le_rfl : n ≤ n) ν) (hw K le_rfl ν) with hc
  set D := (weyl O n n le_rfl ν).map (toK O K) with hD
  have : Module.IsTorsionFree O (MvPolynomial (Fin n × Fin n) K) := polyK_torsionFree
  have : Module.Finite O D := Module.Finite.iff_fg.mpr (weylK_fg ν hν)
  obtain ⟨N, bD⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := D)
  set e : Fin N → MvPolynomial (Fin n × Fin n) K := fun i => (bD i : MvPolynomial (Fin n × Fin n) K) with he_def
  have he : ∀ i, e i ∈ D := fun i => (bD i).2
  have hDV : ∀ x ∈ D, x ∈ dualWeyl K n n ν := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    rw [toK_eq_map]
    exact weylLeDual K n n le_rfl ν hν (sw_weyl_map (algebraMap O K) le_rfl ν y hy)
  have hrep : ∀ x (hx : x ∈ D), x = ∑ i, bD.repr ⟨x, hx⟩ i • e i := by
    intro x hx
    have h := congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at h
    simpa [he_def] using h.symm
  have hsm : ∀ (a : O) (f : MvPolynomial (Fin n × Fin n) K), a • f = algebraMap O K a • f :=
    fun a f => (algebraMap_smul K a f).symm
  have hDspan : ∀ x ∈ D, x ∈ Submodule.span K (Set.range e) := by
    intro x hx
    rw [hrep x hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : dualWeyl K n n ν ≤ Submodule.span K (Set.range e) := by
    rw [← sw_weyl_eq K n n le_rfl ν hν]
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    apply hDspan
    refine Submodule.mem_map.mpr ⟨applyWord O w (hw O le_rfl ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    rw [toK_eq_map, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
  have hliO : LinearIndependent O e := bD.linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  have hli : LinearIndependent K e := (LinearIndependent.iff_fractionRing O K).mp hliO
  set W := Submodule.span K (Set.range e) with hW
  have hWV : W = dualWeyl K n n ν := by
    refine le_antisymm ?_ hspan
    rw [hW, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hDV _ (he i)
  let bW : Module.Basis (Fin N) K W := Module.Basis.span hli
  have hbW : ∀ i, (bW i : MvPolynomial (Fin n × Fin n) K) = e i := fun i =>
    congrArg Subtype.val (Module.Basis.span_apply hli i)
  let Bf : LinearMap.BilinForm K W := LinearMap.mk₂ K (fun x y : W => fockR (x : MvPolynomial (Fin n × Fin n) K) y)
    (fun x x' y => by simp [fockR_add_left]) (fun a x y => by simp [fockR_smul_left])
    (fun x y y' => by simp [fockR_add_right]) (fun a x y => by simp [fockR_smul_right])
  have hBf : ∀ x y : W, Bf x y = fockR (x : MvPolynomial (Fin n × Fin n) K) y := fun _ _ => rfl
  have hnd : Bf.Nondegenerate := by
    constructor
    · intro x hx
      apply Subtype.ext
      refine Top.nondegK K n n le_rfl ν hν x.1 (hWV ▸ x.2) fun P hP => ?_
      rw [fockR_symm]
      exact hx ⟨P, hWV ▸ hP⟩
    · intro y hy
      apply Subtype.ext
      exact Top.nondegK K n n le_rfl ν hν y.1 (hWV ▸ y.2) fun P hP => hy ⟨P, hWV ▸ hP⟩
  let d := Bf.dualBasis hnd bW
  have hd : ∀ i k, fockR (e i) (d k : MvPolynomial (Fin n × Fin n) K) = if i = k then 1 else 0 := by
    intro i k
    have h := LinearMap.BilinForm.apply_dualBasis_left hnd bW k i
    rw [hBf, hbW, fockR_symm] at h
    exact h
  refine ⟨Fin N, inferInstance, inferInstance, e, fun k => c • (d k : MvPolynomial (Fin n × Fin n) K),
    he, ?_, ?_, hspan⟩
  · intro k
    have hkV : c • (d k : MvPolynomial (Fin n × Fin n) K) ∈ dualWeyl K n n ν :=
      Submodule.smul_mem _ _ (hWV ▸ (d k).2)
    refine Top.dualWeylIn O K n n le_rfl ν hν _ hkV fun P hP => ⟨bD.repr ⟨P, hP⟩ k, ?_⟩
    show fockR P (c • (d k : MvPolynomial (Fin n × Fin n) K)) = _
    conv_lhs => rw [hrep P hP]
    rw [fockR_sum_left]
    simp_rw [hsm, fockR_smul_left, fockR_smul_right, hd]
    simp [hc]
  · intro i k
    rw [fockR_smul_right, hd]
    split_ifs <;> simp

end Formalism.L2.PairingIndexBounds.Ent
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.TgtBidet

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.MainNotions.G

variable {O K Kc : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [CharZero K] [Field Kc] [Algebra K Kc]
  {B τ : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (hem : Function.Injective fun x : B × (Fin n × Fin n) => em x.1 x.2)
  (ν : B → Fin n → ℕ) (hν : ∀ b, Antitone (ν b))
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc) (hM : ∀ (o : O), ∀ a ∈ M, algebraMap K Kc (algebraMap O K o) * a ∈ M)

theorem toK_bidet {r n K' : ℕ} (sz : Fin K' → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    toK O K (bideterminant O sz hsz I) = bideterminant K sz hsz I := by
  show map (algebraMap O K) _ = _
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp


include hem hν hh hM in
theorem tgt_bidet (hDB : DualBases) (hFP : FockProd) (hRe : Reorder) (c : B → ℕ) (sz : ∀ b, Fin (c b) → ℕ)
    (hsz : ∀ b k, sz b k ≤ n) (hshape : ∀ b, shapeDeg (sz b) = ν b) (y : MvPolynomial τ Kc)
    (hy : y ∈ Submodule.span Kc {z | ∃ F : B → MvPolynomial (Fin n × Fin n) K, (∀ b, F b ∈ dualWeyl K n n (ν b)) ∧
      z = map (algebraMap K Kc) (∏ b, rename (em b) (F b))})
    (hp : ∀ I : ∀ b, ∀ k, Fin (sz b k) → Fin n,
      ∃ a ∈ M, fockR y (map (algebraMap K Kc) (∏ b, rename (em b) (rowAct K (h b).transpose (bideterminant K (sz b) (hsz b) (I b))))) =
        a * ∏ b, cN Kc (ν b)) :
    y ∈ AddSubgroup.closure {z | ∃ a ∈ M, ∃ F : B → MvPolynomial (Fin n × Fin n) K,
      (∀ b, F b ∈ deltaL O K n (ν b) (h b)) ∧ z = a • map (algebraMap K Kc) (∏ b, rename (em b) (F b))} := by
  refine tgt_abs (O := O) em hem ν hν h hi hh M hDB hFP y hy fun Q hQ => ?_
  let T : Submodule O (MvPolynomial τ K) :=
    { carrier := {Z | ∃ a ∈ M, fockR y (map (algebraMap K Kc) Z) = a * ∏ b, cN Kc (ν b)}
      add_mem' := by
        rintro Z Z' ⟨a, ha, h1⟩ ⟨a', ha', h2⟩
        refine ⟨a + a', M.add_mem ha ha', ?_⟩
        rw [map_add (f := _), fockR_comm, fockR_add_left, fockR_comm _ y, fockR_comm _ y, h1, h2, add_mul]
      zero_mem' := ⟨0, M.zero_mem, by rw [map_zero, fockR_comm, fockR_zero_left, zero_mul]⟩
      smul_mem' := by
        rintro o Z ⟨a, ha, h1⟩
        refine ⟨_, hM o a ha, ?_⟩
        rw [← algebraMap_smul K o Z, smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, fockR_comm, fockR_smul_left, fockR_comm, h1,
          mul_assoc] }
  refine prod_span (R := O) (fun b => Set.range fun I : ∀ k, Fin (sz b k) → Fin n =>
    rename (em b) (rowAct K (h b).transpose (bideterminant K (sz b) (hsz b) I))) T ?_ _ ?_
  · intro f hf
    choose I hI using hf
    obtain ⟨a, ha, h1⟩ := hp I
    refine ⟨a, ha, ?_⟩
    rw [← Finset.prod_congr rfl fun b _ => hI b]
    exact h1
  · intro b
    have h1 := hQ b
    rw [standardMonomialSpanDomain O n n (ν b), Submodule.map_span] at h1
    have h2 := Submodule.mem_map_of_mem (f := (((rename (em b) : MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial τ K).comp
      (rowAct K (h b).transpose)).toLinearMap).restrictScalars O) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨_, ⟨K', sz', hsz', I', hs', rfl⟩, rfl⟩, rfl⟩
    obtain ⟨I'', hI''⟩ := hRe K n n K' (c b) sz' (sz b) hsz' (hsz b) (hs'.trans (hshape b).symm) I'
    refine ⟨I'', ?_⟩
    rw [toK_bidet, hI'']
    rfl

end Formalism.L2.PairingIndexBounds.Ent
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.AdmissibleGeneralLatticeTuple

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem admissible_general_lattice_tuple (hS : XShape) (hBrS : XBrS) (hBrT : XBrT) (hInj : XInj) (hSp : XSpanN) (hMid : XMid) (hU : XUnit) (hE : XEdge)
    (Oc : Subring Kc) (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc)
    (hO : ∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc)
    (j : ℕ) (La : X.Lt j) (c' : X.Lv.comp (j + 1)) (L' L'' : (X.Pj (j + 1)).Tup) (i0 : X.Pl → ℕ)
    (h1 : (X.Pj j).IsLatTup La.2) (h2 : (X.Pj (j + 1)).IsLatTup L') (h3 : ∀ v, i0 v ≤ X.G.P.r)
    (h4 : ∀ v' : Fin (X.Pj (j + 1)).nV, (i0 (X.vB (j + 1) v') = 0 ∧ L'' v' = L' v') ∨
      (1 ≤ i0 (X.vB (j + 1) v') ∧ IsEdge p ((X.Pj (j + 1)).n' v') (i0 (X.vB (j + 1) v')) ⟨L'' v', L' v'⟩)) :
    ∃ φ : Frm X j La (c', L''), ∀ (f : MvPowerSeries (X.ZA j) Kc) (gg : ℝ),
      (∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), geX p Oc (AddMonoidAlgebra.coeff (applyD (X.PI j I i0) f) n) gg) →
      ∀ G ∈ (X.Pj j).HtupW La.2,
        ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) •
          (((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
            (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L''))⁻¹) •
              delF X Kc j G (linSub (bc Kc φ) f))) ∈
        AddSubgroup.closure {y' | ∃ a : Kc, geX p Oc a gg ∧ ∃ z ∈ (X.Pj (j + 1)).HtupW L',
          y' = a • map (algebraMap X.G.Kf Kc) z} := by
  classical
  have cz : CharZero X.G.Kf := (algebraMap X.G.Kf Kc).charZero
  obtain ⟨g', h', hg', hh', hmF⟩ := hE p X j L' L'' i0 h2 h4
  obtain ⟨φ0⟩ := exists_frm X j La (c', L') h1 h2
  let φ : Frm X j La (c', L'') := ⟨φ0.g, g', φ0.hg, hg'⟩
  refine ⟨φ, fun f gg hf G hG => ?_⟩
  set ft := linSub (bc Kc φ) f with hft
  set S1 : X.G.Kf := ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
    ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
      (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L''))⁻¹)) with hS1
  set s' : X.G.Kf := sX X (j + 1) (fun v => (h' v : Matrix _ _ _)) with hs'
  have hs'0 : s' ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (mF_det_ne X (j + 1) b (h' b.1))
  have hs'e : s' = ∏ b : BX X, (mF X (j + 1) b (g' b.1 : Matrix _ _ _) * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)) :=
    Finset.prod_congr rfl fun b _ => by rw [hmF b]
  have hy1 := tgt_bidet (O := X.G.O) (Kc := Kc) (emX X (j + 1)) (hInj p X (j + 1)).1 (nuT X j) (nuT_antitone X hS j)
    (fun b => mF X (j + 1) b (h' b.1)) (fun b => mF X (j + 1) b ((h' b.1)⁻¹ : GL _ _)) (fun b => mF_inv_mul X (j + 1) b (h' b.1))
    (MG p Oc hval gg) (fun o a ha => geX_mul (hO o) ha) dual_bases_holds fock_product_holds reorder_holds (cX X j) (szT X j)
    (szT_le X j) (shape_szT X hS j) ((S1 * s'⁻¹) • delF X Kc j G ft)
    (by
      rw [← algebraMap_smul Kc (S1 * s'⁻¹)]
      exact Submodule.smul_mem _ _ (xSpan X Kc hS hBrS hInj hSp j La.2 φ0.g φ0.hg ft G hG))
    (fun I => by
      have := xPair X Kc hS hBrS hInj hMid hU Oc hval hO j La (c', L'') φ i0 h3 f gg hf G hG I
      rw [← hS1, ← hs'e] at this
      simp only [hmF]
      exact this)
  have htr : ∀ z ∈ AddSubgroup.closure {z | ∃ a ∈ MG p Oc hval gg,
      ∃ F : BX X → MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) X.G.Kf,
        (∀ b, F b ∈ deltaL X.G.O X.G.Kf (NJ X (j + 1)) (nuT X j b) (mF X (j + 1) b (h' b.1))) ∧
          z = a • map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b) (F b))},
      s' • z ∈ AddSubgroup.closure {y' | ∃ a : Kc, geX p Oc a gg ∧ ∃ z ∈ (X.Pj (j + 1)).HtupW L',
        y' = a • map (algebraMap X.G.Kf Kc) z} := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, F, hF, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨a, ha, s' • ∏ b, rename (emX X (j + 1) b) (F b), ?_, ?_⟩
      · refine hBrT p X (hinjX X) (j + 1) L' (fun v => h' v) (fun v => (Matrix.isUnit_iff_isUnit_det _).1 (h' v).isUnit) hh' F ?_
        intro b
        rw [(hS p X j b).2.1]
        exact hF b
      · rw [smul_comm, smul_eq_C_mul (a := s'), map_mul, map_C, ← smul_eq_C_mul, algebraMap_smul]
    | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
    | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx
  have := htr _ hy1
  rw [smul_smul, mul_comm s', mul_assoc, inv_mul_cancel₀ hs'0, mul_one, hS1, mul_smul] at this
  exact this

end Formalism.L2.PairingIndexBounds.Ent
end
end
end
