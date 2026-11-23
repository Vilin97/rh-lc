module

public import Formalism.SharpRestriction.GlobalSchurBounds.LinkGLOBAL7Tied4
public import Formalism.LocalToGlobal.GlobalTheory.ColValOfTiedSOfFin
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.Columns.PolyFn
public import Formalism.LocalToGlobal.GlobalTheory.ColMemOfIsLocBasis
import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionFamilyOf
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.LocalToGlobal.GlobalTheory.MemIffOfLocBasisG
public import Formalism.LocalToGlobal.GlobalTheory.SigDEqStar
public import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGlob
public import Formalism.LocalToGlobal.GlobalTheory.GramNDetNe
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.NfAllSmulSelfRe
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ExistsPrimeToLe
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Mathlib.Tactic.Linter.Style
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr

-- Source module: Formalism.LocalToGlobal.GlobalTheory.NatInvMemIntW

section

@[expose] public section

noncomputable section

open Matrix NumberField

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def eqv (D : D7) : (D.sp.X 0).V ≃ₗ[D.host.E] (Fin (D.R.N 0) → D.host.E) :=
  (D.sp.X 0).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm)

theorem mem_clsCrd_iff {u : D.what₂.Word} (c : (D.mem u).C.cls 0) (z : Fin (D.R.N 0) → D.host.E) :
    z ∈ Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c ↔ (eqv D).symm z ∈ D.clsLat u 0 c := by
  unfold Formalism.L2.Forms.clsCrd
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    exact (eqv D).symm_apply_apply y
  · intro h
    exact ⟨_, h, (eqv D).apply_symm_apply z⟩

def vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (a : Fin (D.R.N 0)) : (D.sp.X 0).V :=
  (eqv D).symm fun r => Y r a

variable {u : D.what₂.Word} (B : ColBase D u)

theorem sum_gamma (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (a : Fin (D.R.N 0)) :
    ∑ i, (Mb B c τ * Y.map (B.rho τ)) i a • (B.Q c τ).b ((B.eQ c τ).symm i) = B.bc c τ (vcol Y a) := by
  have hfr : ∀ r : Fin (D.R.N 0), (eqv D).symm (Pi.single r 1) =
      (D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r) := by
    intro r
    rw [LinearEquiv.symm_apply_eq]
    ext r'
    simp [eqv, Pi.single_apply]
    rw [Finsupp.single_apply]
    split_ifs <;> simp_all [Fin.cast_inj]
  have hz : (fun r => Y r a) = ∑ r, Y r a • (Pi.single r (1 : D.host.E) : Fin (D.R.N 0) → D.host.E) := by
    ext r'
    simp [Finset.sum_apply, Pi.single_apply]
  have hbc : B.bc c τ (vcol Y a) = ∑ r, B.rho τ (Y r a) •
      B.bc c τ ((D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r)) := by
    unfold vcol

    rw [hz, map_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, B.bc_smul, hfr]
  have hexp : ∀ v : (B.Q c τ).V,
      v = ∑ i, (B.Q c τ).b.repr v ((B.eQ c τ).symm i) • (B.Q c τ).b ((B.eQ c τ).symm i) := by
    intro v
    rw [Equiv.sum_comp (B.eQ c τ).symm (fun j => (B.Q c τ).b.repr v j • (B.Q c τ).b j)]
    exact ((B.Q c τ).b.sum_repr v).symm
  rw [hbc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Mb, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  conv_rhs => rw [hexp (B.bc c τ ((D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r)))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm]

theorem rhoC_mem_intW (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (y : D.host.E) (s : ℕ)
    (hs : ¬ D.what₂.places.resChar w ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    rhoC D τ y ∈ intW D.what₂.places w := by
  obtain ⟨k, hk⟩ := hy
  have hint : IsIntegral ℤ (rhoC D τ (k : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe k).map (rhoC D τ).toIntAlgHom
  have hk' : (s : D.what₂.LL) * rhoC D τ y ∈ intW D.what₂.places w := by
    have h1 : rhoC D τ ((s : D.host.E) * y) = (s : D.what₂.LL) * rhoC D τ y := by
      rw [map_mul, map_natCast]
    rw [← h1, ← hk]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_int_mem D w ⟨_, hint⟩
  have hinv : ((s : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w := by
    change (0 : WithTop ℤ) ≤ D.what₂.places.val w ((s : D.what₂.LL))⁻¹
    have h0 : D.what₂.places.val w ((s : D.what₂.LL)) = 0 :=
      Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_nat_eq_zero (s := s) (hs := hs)
    rw [AddValuation.map_inv, h0, neg_zero]
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h
    apply hs
    have h2 : s = 0 := by exact_mod_cast h
    rw [h2]
    exact dvd_zero _
  have h3 := (intW D.what₂.places w).mul_mem hinv hk'
  rwa [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at h3

theorem natInv_mem_intW (w : D.what₂.places.Pl) (t : ℕ) (ht : ¬ D.what₂.places.resChar w ∣ t) :
    ((t : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w := by
  change (0 : WithTop ℤ) ≤ D.what₂.places.val w ((t : D.what₂.LL))⁻¹
  have h0 : D.what₂.places.val w ((t : D.what₂.LL)) = 0 :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_nat_eq_zero (s := t) (hs := ht)
  rw [AddValuation.map_inv, h0, neg_zero]

theorem locBasis_gamma (hB : B.rho = rhoC D) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau)
    (Y : GL (Fin (D.R.N 0)) D.host.E)
    (hY : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y) :
    Formalism.MainNotions.flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ)
      (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ)) := by
  have hp1 : ¬ D.what₂.places.resChar w ∣ 1 := (D.what₂.places.resChar_prime w).not_dvd_one
  have hg : ∀ a, ∑ i, (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ)) i a •
      (B.Q c τ).b ((B.eQ c τ).symm i) = B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) :=
    fun a => sum_gamma B c τ _ a
  have hsmul : ∀ (r : D.what₂.LL) (hr : r ∈ intW D.what₂.places w) (v : (B.Q c τ).V),
      r • v = (⟨r, hr⟩ : intW D.what₂.places w) • v := fun r hr v => by rw [Subring.smul_def]
  have hcolv : ∀ v : Fin (D.R.N 0) → D.host.E, (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ v =
      ∑ a, v a • (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a) := by
    intro v
    ext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul (isUnit_iff_ne_zero.2 (Mb_det_ne B c τ)) ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit Y)).map _
  · simp only [hg]
    apply le_antisymm
    · unfold locW
      rw [Submodule.span_le]
      intro x hx
      rw [SetLike.mem_coe, B.bc_L c τ] at hx
      refine Submodule.span_induction (p := fun x _ => x ∈ Submodule.span (intW D.what₂.places w)
        (Set.range fun a => B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a))) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨y, hy, rfl⟩
        have hz : eqv D y ∈ Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c := by
          rw [mem_clsCrd_iff, LinearEquiv.symm_apply_apply]
          exact hy
        obtain ⟨s, hs, hint⟩ := (hY (eqv D y)).1 ⟨1, hp1, by rw [Nat.cast_one, one_smul]; exact hz⟩
        have h1 : (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
            ((((Y⁻¹ : GL (Fin (D.R.N 0)) D.host.E)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ eqv D y) =
            eqv D y := by
          rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
        have hyz : y = ∑ a, ((((Y⁻¹ : GL (Fin (D.R.N 0)) D.host.E)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
            eqv D y) a • vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a := by

          conv_lhs => rw [← (eqv D).symm_apply_apply y, ← h1, hcolv, map_sum]
          simp only [LinearEquiv.map_smul]
          rfl

        rw [hyz, map_sum]
        refine Submodule.sum_mem _ fun a _ => ?_
        rw [B.bc_smul, hB, hsmul _ (rhoC_mem_intW w τ _ s hs (hint a))]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · exact zero_mem _
      · intro x y _ _ hx hy
        exact add_mem hx hy
      · intro r x _ hx
        have hr : r • x = (⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_int_mem D w r⟩ : intW D.what₂.places w) • x := by
          rw [Subring.smul_def]
          exact (algebraMap_smul D.what₂.LL r x).symm
        rw [hr]
        exact Submodule.smul_mem _ _ hx
    · unfold locW
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have hcol : (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a) =
          (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ Pi.single a 1 := by
        ext r
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      obtain ⟨s, hs, hsm⟩ := (hY (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a)).2 ⟨1, hp1, fun b => by
        rw [hcol, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Nat.cast_one, one_mul]
        by_cases hb : b = a
        · subst hb
          exact ⟨1, by simp⟩
        · exact ⟨0, by simp [Pi.single_apply, hb]⟩⟩
      rw [SetLike.mem_coe, mem_clsCrd_iff, LinearEquiv.map_smul] at hsm
      have hQ : B.bc c τ ((s : D.host.E) • vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) ∈
          (B.Q c τ).L := by
        rw [B.bc_L c τ]
        exact Submodule.subset_span ⟨_, hsm, rfl⟩
      rw [B.bc_smul, map_natCast] at hQ
      have hs0 : (s : D.what₂.LL) ≠ 0 := by
        intro h
        apply hs
        have h2 : s = 0 := by exact_mod_cast h
        rw [h2]
        exact dvd_zero _
      have h4 : B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) =
          (⟨_, natInv_mem_intW w s hs⟩ : intW D.what₂.places w) •
            ((s : D.what₂.LL) • B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a)) := by
        rw [Subring.smul_def, smul_smul, inv_mul_cancel₀ hs0, one_smul]
      rw [SetLike.mem_coe]
      beta_reduce
      rw [h4]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hQ)

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.TransposeBaseMatrixInfinity

section

@[expose] public section

noncomputable section

open Matrix NumberField

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem embT_sigD (τ : D.what₂.Tau) (a : D.host.E) :
    Formalism.L2.Forms.embT D τ (Formalism.L2.Forms.sigD D a) = starRingEnd ℂ (Formalism.L2.Forms.embT D τ a) := by
  haveI := D.host.isCMField_hostE
  show D.host.emb (D.eTau τ : D.R.GG) (Formalism.L2.Forms.sigD D a) = starRingEnd ℂ (D.host.emb (D.eTau τ : D.R.GG) a)
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ a

theorem embLL_rhoC (τ : D.what₂.Tau) (a : D.host.E) :
    D.what₂.embLL (rhoC D τ a) = starRingEnd ℂ (Formalism.L2.Forms.embT D τ a) := by
  rw [rhoC_conj D.what₂.embLL τ a]
  congr 1
  exact (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_embT_eq D τ a).symm

theorem gramN_sig (i j : Fin (D.R.N 0)) :
    Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) i j = Formalism.L2.Forms.sigD D (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) j i) := by
  letI := D.host.cmStar
  simp only [Formalism.L2.Forms.gramN, Matrix.reindex_apply, Matrix.submatrix_apply, Formalism.BasicNotions.HSpace.gram]
  first
  | exact ((D.sp.X 0).herm _ _).symm
  | exact ((D.sp.X 0).herm.eq _ _).symm

def BaseBlockInverse (Y : GL (Fin (D.R.N 0)) D.host.E) : GL (Fin (D.R.N 0)) D.host.E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *
      Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (by
    rw [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero _).2 (Matrix.isUnits_det_units Y).ne_zero) gramN_det_ne)

theorem B0inv_coe (Y : GL (Fin (D.R.N 0)) D.host.E) :
    ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) =
      Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *
        Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) := rfl

theorem transpose_base_matrix_infinity (Y : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ)).map
      D.what₂.embLL)ᵀ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ := by
  rw [B0inv_coe]
  ext i j

  simp only [Matrix.transpose_apply, Matrix.map_apply, Formalism.L2.Forms.atInf, Formalism.UG.cT, Matrix.mul_apply, map_sum, map_mul,
  AlgHom.coe_toRingHom]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [embLL_rhoC, embLL_rhoC, gramN_sig j k, embT_sigD, embT_sigD, starRingEnd_self_apply, mul_comm]

variable {u : D.what₂.Word} (B : ColBase D u)

theorem h_T_mul (hB : B.rho = rhoC D) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (Y : GL (Fin (D.R.N 0)) D.host.E) :
    (((Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹ *
        ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)).map D.what₂.embLL)ᵀ *
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ = 1 := by
  have hMb : IsUnit (Mb B c τ).det := isUnit_iff_ne_zero.mpr (Mb_det_ne B c τ)
  have hGY : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
      (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_mul]
    exact (map_ne_zero _).2 (mul_ne_zero gramN_det_ne (Matrix.isUnits_det_units Y).ne_zero)
  have hA : (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (rhoC D τ))⁻¹ *
      (Mb B c τ * ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map (rhoC D τ))⁻¹) =
      ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
        (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ))⁻¹ := by
    rw [Matrix.map_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Mb B c τ)⁻¹, Matrix.nonsing_inv_mul _ hMb, Matrix.one_mul]
  rw [gC_coe, hB, hA, ← transpose_base_matrix_infinity Y τ, ← Matrix.transpose_mul, ← Matrix.map_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hGY)]
  simp

theorem isUnit_base_inverse_infinity (Y : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    IsUnit (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det := by
  unfold Formalism.L2.Forms.atInf
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (Matrix.isUnits_det_units (BaseBlockInverse Y)).map _

theorem clause_iff (T0 : Formalism.L2.Forms.Forms0 D u) (hB : B.rho = rhoC D) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0)
    (Y : GL (Fin (D.R.N 0)) D.host.E)
    (hY : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y)
    (x : ((D.fm u).lat 0).V) :
    (∀ Bb : GL (Fin (D.R.N 0)) D.host.E,
      Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
        (dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
          (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c)) Bb →
      ∃ P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0),
        ∀ z, (D.fm u).emb 0 x c z =
          Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0))
            (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (Bb⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) P (T0.val0.eY z)) ↔
    Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
      (fun τ => (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹)
      (coT T0 (gC B) x c) ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w ((D.fm u).lam 0) := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  set p := co0 T0 x c with hp
  set lam := (D.fm u).lam 0 with hlam
  set Gf := Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) with hGf
  set s0 := Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0) with hs0
  set hh : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    ((Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹ *
      ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)).map D.what₂.embLL with hhh
  set N0 : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
    Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) with hN0
  have hK : (fun τ => (hh τ)ᵀ * N0 τ) = 1 := funext fun τ => h_T_mul B hB c τ Y
  have hs : ∀ τ, s0 τ = (lam τ).detShift := fun τ => by rw [hs0, Formalism.L2.Forms.lamT_zero]; rfl
  have hemb : ∀ z, (D.fm u).emb 0 x c z =
      Formalism.L2.Forms.fnOf Gf s0 1 (MvPolynomial.map D.what₂.embLL p) (T0.val0.eY z) := fun z => pol_spec T0 x c z
  have hRHS : Formalism.MainNotions.flipTwoThree.actAll lam
      (fun τ => (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹)
      (coT T0 (gC B) x c) ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w lam ↔
      Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p) ∈ Formalism.L2.Forms.IntSpan D w lam := by
    rw [coT_apply, actAll_comp, mem_intSpanAt_iff_map, map_actAll]
  have hfn : Formalism.L2.Forms.fnOf Gf s0 N0 (Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p)) =
      Formalism.L2.Forms.fnOf Gf s0 1 (MvPolynomial.map D.what₂.embLL p) := by
    have h1 := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.fnOf_mul Gf s0 (fun τ => (hh τ)ᵀ) N0 (MvPolynomial.map D.what₂.embLL p)
    rw [hK] at h1
    rw [h1, actAll_eq_subP, MvPolynomial.smul_eq_C_mul]
    congr 3
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_transpose, hs]
  have hB0 : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
        (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c)) (BaseBlockInverse Y)⁻¹ :=
    isLocBasis_dual (D.what₂.places.resChar w) _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).fg hY _
      (by rw [inv_inv]; rfl)
  have hN0' : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((((BaseBlockInverse Y)⁻¹)⁻¹ : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = N0 := by
    rw [inv_inv]
  rw [hRHS]
  constructor
  · intro hAll
    obtain ⟨P, hP, hPz⟩ := hAll _ hB0
    rw [hN0'] at hPz
    have hPe : Formalism.L2.Forms.fnOf Gf s0 N0 P =
        Formalism.L2.Forms.fnOf Gf s0 N0 (Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p)) := by
      funext y
      obtain ⟨z, rfl⟩ := T0.val0.eY.surjective y
      rw [hfn, ← hemb, hPz]
    have := Formalism.L2.Col.fnOf_injective Gf s0 N0 (isUnit_base_inverse_infinity Y) (Formalism.MainNotions.Ext.Lw.frOne Gf) hPe
    rw [← this]
    exact hP
  · intro hQ Bb hBb
    obtain ⟨Q₂, hQ₂, hQe⟩ := basis_change D w lam Gf s0 hB0 hBb _ hQ
    rw [hN0'] at hQe
    refine ⟨Q₂, hQ₂, fun z => ?_⟩
    rw [hemb, ← hfn, hQe]

theorem finCo_of (T : ∀ u : D.what₂.Word, Formalism.L2.Forms.Forms0 D u) (u : D.what₂.Word) (B : ColBase D u)
    (hB : B.rho = rhoC D) : FinCo (T u) B := by
  intro w
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hex : ∀ c : (D.mem u).C.cls 0, ∃ Y : GL (Fin (D.R.N 0)) D.host.E,
      Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
        (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y := by
    intro c
    refine Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis
      (l := D.what₂.places.resChar w) (K := D.host.E) _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).fg ?_
    have hLat := D.clsLat_lat u 0 c
    unfold Formalism.L2.Forms.clsCrd
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLat.span_eq_top,
      Submodule.map_top, LinearEquiv.range]
  choose Y hY using hex
  refine ⟨fun c τ => Mb B c τ * (Y c : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ),
    fun c τ => locBasis_gamma B hB w c τ (Y c) (hY c), fun x => ?_⟩
  rw [Formalism.L2.G.Cmp.locWCrit_proved T u w x]
  exact forall_congr' fun c => clause_iff B (T u) hB w c (Y c) (hY c) x

theorem colValOfTiedS_holds : Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  colValOfTiedS_of_fin fun _ F _ u B hB => finCo_of (fun u => (F.forms u).to0) u B hB

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end
end

-- Source module: Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfBranchIdentitiesAndMultiplicity

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

variable {eps : ℝ}

theorem tCV_of_ties (Fm : FamP eps) (tCl : tCVTies Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u) :=
  tCV_of_tied Fm ColValS.colValOfTiedS_holds tCl

end Formalism.MainNotions

end
end
end
