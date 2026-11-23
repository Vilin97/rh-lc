module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiAlgUnitInert
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLambdaCharacterNormOneIdeleEqPPowStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersCharOnNormOneIdelesMulUnramifiedClassValueStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiAMemRange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplAlgLocAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterUniformizingIdeleMemCoeffFieldStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponentsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.VEqKZeroOfNormOne
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteNormalisingCharPowValuesInCoeffField

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.ChiPow

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem exists_upts_det {n : ℕ} (hn : 0 < n) (Gm : Matrix (Fin n) (Fin n) E) (C : GL (Fin n) E)
    (hC : cT (σ : E →+* E) C.1 * C.1 = Gm) (x : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ)
    (hx : (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * sigR σ _ x = 1) :
    ∃ Y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), Y ∈ UPts σ Gm (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det Y = x := by
  set R := FiniteAdeleRing (𝓞 F) F
  let f : Fin n → (E ⊗[F] R)ˣ := Pi.mulSingle ⟨0, hn⟩ x
  have hf : f = Pi.mulSingle ⟨0, hn⟩ x := rfl
  let d : GL (Fin n) (E ⊗[F] R) := Units.map (Matrix.diagonalRingHom (Fin n) (E ⊗[F] R)).toMonoidHom
    (MulEquiv.piUnits.symm f)
  have hd : (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = Matrix.diagonal (fun k => ((f k : (E ⊗[F] R)ˣ) : E ⊗[F] R)) := rfl
  let Cb := bc (inclE (F := F) R) C
  refine ⟨Cb⁻¹ * d * Cb, ?_, ?_⟩
  · have hsig : (inclE (F := F) R).comp (σ : E →+* E) = (sigR σ R).comp (inclE R) := by
      ext e
      simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
    have hG : Gm.map (inclE (F := F) R) = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
      rw [← hC, Matrix.map_mul, ← Formalism.UG.P.cT_map (σ : E →+* E) (sigR σ R) (inclE R) hsig]
      rfl
    have hdd : cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 := by
      rw [hd]
      unfold cT
      rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      by_cases hk : k = ⟨0, hn⟩
      · subst hk
        rw [hf, Pi.mulSingle_eq_same, mul_comm]
        exact hx
      · rw [hf, Pi.mulSingle_eq_of_ne hk, Units.val_one, map_one, one_mul]
    have h1 : cT (sigR σ R) ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
        cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 := by
      rw [← cT_mul, Units.mul_inv, cT_one]
    have h2 : (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 :=
      Units.mul_inv Cb
    show cT (sigR σ R) (((Cb⁻¹ * d * Cb : GL (Fin n) (E ⊗[F] R))) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * Gm.map (inclE (F := F) R) *
      (((Cb⁻¹ * d * Cb : GL (Fin n) (E ⊗[F] R))) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = Gm.map (inclE (F := F) R)
    rw [hG, Units.val_mul, Units.val_mul, cT_mul, cT_mul]
    calc _ = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          (cT (sigR σ R) ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          ((Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
            simp only [Matrix.mul_assoc]
      _ = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          (cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (d : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
            rw [h1, h2]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hdd, Matrix.mul_one]
  · ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul, hd, Matrix.det_diagonal]
    rw [← Units.coe_prod, hf, Finset.prod_pi_mulSingle', if_pos (Finset.mem_univ _)]
    calc _ = (Matrix.det ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          Matrix.det (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R))) * (x : E ⊗[F] R) := by ring
      _ = _ := by rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]

end Gen

end GlobalTheory.TwV.Xc.ChiPow

namespace GlobalTheory.TwV.Xc.ChiPow



theorem tw_ch_rat {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}
    (S : StepIn M i hi G) (β : S.Ch) (hr : S.ChRat β)
    (X : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = ((S.tw β).ch X : ℂ) := by
  obtain ⟨cl, hcl⟩ := (S.K β).y_bij.2 (Quotient.mk'' X)
  have hrel := Quotient.eq''.1 hcl
  rw [DoubleCoset.rel_iff] at hrel
  obtain ⟨h, hh, k, hk, hX⟩ := hrel
  obtain ⟨γ, hγ, hγh⟩ := hh
  have h1 := (S.tw β).ch_rat γ hγ h hγh.symm
  have h2 := (S.tw β).ch_U k hk
  obtain ⟨rc, hrc⟩ := hr cl
  refine ⟨(∏ τ, (tEL D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det) ^ (cTw D i))⁻¹ * rc, ?_⟩
  rw [hX, map_mul (S.tw β).ch, map_mul (S.tw β).ch, h2, mul_one, Units.val_mul, map_mul D.what₂.embLL, hrc, map_inv₀, map_prod]
  congr 1
  have e1 : ∏ τ, D.what₂.embLL (tEL D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det ^ cTw D i) =
      ∏ τ, (embT D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det) ^ cTw D i :=
    Finset.prod_congr rfl fun τ _ => by rw [map_zpow₀, tEL_emb]
  rw [e1]
  exact (eq_inv_of_mul_eq_one_left h1).symm

end GlobalTheory.TwV.Xc.ChiPow

namespace GlobalTheory.TwV.Xc



theorem chiI_pow_rat : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), (sysS H X std).Lv.comp j → ∀ x ∈ U1 (sigD D), ∃ r : D.what₂.LL, D.what₂.embLL r = chiI J x ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj c x hx
  cases j with
  | zero => exact ⟨1, by simp⟩
  | succ i =>
    have hi : i + 1 ≤ D.R.m := hj
    have hxc : (x : AfE D.host.F D.host.E) * sigR (sigD D) _ x = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hx)
    obtain ⟨Y, hY, hYd⟩ := ChiPow.exists_upts_det (sigD D) Nat.one_pos (1 : Matrix (Fin 1) (Fin 1) D.host.E) 1
      (by rw [Units.val_one, cT_one, Matrix.one_mul]) x hxc
    have hex : ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x := ⟨⟨Y, hY⟩, hYd⟩
    have hchi : chiI J x = ((D.chiD (J.dtU hex.choose) : ℂˣ) : ℂ) := by
      unfold chiI
      rw [dite_eq_left hex]
    obtain ⟨Z, hZ, hZd⟩ := ChiPow.exists_upts_det (sigD D) (D.R.N_pos (i + 1)) (gramN D (i + 1) hi) (J.A.crd (i + 1) hi)
      (J.pins.crd_orth (i + 1) hi) x hxc
    let β := ((I.at' i hi).st.eC.symm c).1
    have htw := J.tw i hi β ⟨Z, hZ⟩ hex.choose (hex.choose_spec.trans hZd.symm)
    obtain ⟨r, hr⟩ := ChiPow.tw_ch_rat (I.at' i hi).st β (H.core i hi β).chRat ⟨Z, hZ⟩
    have ht : (sysS H X std).t = D.R.t := (GlobalTheory.TwV.DelB.sysS_ranks S).2.1
    refine ⟨r, ?_⟩
    rw [hr, htw, hchi, ht, Units.val_zpow_eq_zpow_val]
    rfl

end GlobalTheory.TwV.Xc

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteNormalisingCharPowValuesInCoeffFieldStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_normalisingCharPow_values_in_coeffField : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), (sysS H X std).Lv.comp j → ∀ x ∈ U1 (sigD D), ∃ r : D.what₂.LL, D.what₂.embLL r = chiI J x ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) := by
  first | exact @GlobalTheory.TwV.Xc.chiI_pow_rat | exact GlobalTheory.TwV.Xc.chiI_pow_rat | (intros; apply GlobalTheory.TwV.Xc.chiI_pow_rat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoUnitsAtPlaceUniformizingIdele

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.TwoUnits

theorem embLL_mem (D : D7) (z : D.what₂.LL) : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral z).map D.what₂.embLL.toRatAlgHom

theorem lamC_zpow {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (n : ℤ) :
    TaylorLogMetric.lamC lam (x ^ n) = TaylorLogMetric.lamC lam x ^ n := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (zpow_mem hx n), Formalism.L2.Ker.lamC_of_mem lam hx, ← map_zpow₀]
  congr 1

theorem lamC_inv {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x⁻¹ = (TaylorLogMetric.lamC lam x)⁻¹ := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (inv_mem hx), Formalism.L2.Ker.lamC_of_mem lam hx, ← map_inv₀]
  rfl

end GlobalTheory.TwV.Xc.TwoUnits


open GlobalTheory.TwV.Xc.TwoUnits in

theorem GlobalTheory.TwV.Xc.two_units : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => KIn t → S.Pos → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, (sysS H X std).Lv.comp j → (sysS H X std).Lv.comp (j + 1) → ∃ a b : (sysS H X std).G.Kf, (sysS H X std).vEqK a 0 ∧ (sysS H X std).vEqK b 0 ∧ S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) ∧ S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hKIn hPos v π hπ j hj hcj hcj1
  have hπU : π ∈ U1 (sigD D) := hπ.1
  obtain ⟨rm, hrm⟩ := GlobalTheory.T.stepCharacter_uniformizingIdele_mem_coeffField S hD hS hKIn v π hπ j hj
  obtain ⟨ra, hra⟩ := GlobalTheory.T.kernelSite_normalisingCharPow_values_in_coeffField S hD hS j hj.le hcj π hπU
  obtain ⟨rb, hrb⟩ := GlobalTheory.T.kernelSite_normalisingCharPow_values_in_coeffField S hD hS (j + 1) hj hcj1 π hπU
  have hfill := GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hS j hj hcj1
  have hnorm := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj hfill π hπU
  have hord : ∀ v' : (sysS H X std).Pl, ordA (A0 J) v' π = if v' = v then 1 else 0 := by
    intro v'
    split_ifs with h
    · subst h; exact hπ.2.2
    · exact ((GlobalTheory.TwV.Xc.OrdA.ordA_props _ _ _ _ _ (A0 J) (GlobalTheory.TwV.LbB.locInt_locAt _) hS.1 v').2.2.2 v (Ne.symm h) π hπ.2.1)
  have hsum : (∑ v' : (sysS H X std).Pl, (sysS H X std).vm v' (j + 1) * ordA (A0 J) v' π) = (sysS H X std).vm v (j + 1) := by
    rw [Finset.sum_eq_single v]
    · rw [hord v, if_pos rfl, mul_one]
    · intro b _ hb; rw [hord b, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ v) h
  rw [hsum] at hnorm
  obtain ⟨𝔞, h𝔞, hχ⟩ := (GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue S hD hS).2.2.2 π hπU
  have hcur := S.curve
  have hp2 : D.what₂.places.resChar w ≠ 2 := by have := hcur.1; omega
  obtain ⟨hQ, -, hone⟩ := GlobalTheory.TwV.Xc.chi_alg_unit_inert D _ S.lam t.χ hcur.2.2.2.2.2.2.1 hp2 hcur.2.2.1 𝔞 h𝔞
  rw [← hχ] at hQ hone
  have hpK : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero)
  have hmQ : S.muT (j + 1) π ∈ TaylorLogMetric.Qbar := hrm ▸ embLL_mem D rm
  have hK : ∀ r : D.what₂.LL, S.E.iK (ex.cmp.embW u w hg r) = TaylorLogMetric.lamC S.lam (D.what₂.embLL r) := fun r =>
    (S.hK r (embLL_mem D r)).trans (Formalism.L2.Ker.lamC_of_mem S.lam (embLL_mem D r)).symm
  refine ⟨((D.what₂.places.resChar w : ℕ) : (sysS H X std).G.Kf) ^ (-((sysS H X std).vm v (j + 1))) * ex.cmp.embW u w hg (rm * ra),
    ((D.what₂.places.resChar w : ℕ) : (sysS H X std).G.Kf) ^ ((sysS H X std).vm v (j + 1)) * ex.cmp.embW u w hg (rm⁻¹ * rb⁻¹), ?_, ?_, ?_, ?_⟩
  · apply GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb
    show ‖S.E.iK _‖ = 1
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, hrm, hra, Formalism.L2.Ker.lamC_mul S.lam hmQ (zpow_mem hQ _), lamC_zpow S.lam hQ,
      norm_mul, norm_mul, norm_zpow, norm_zpow, hnorm, hone, one_zpow, mul_one, ← zpow_add₀ hpK, neg_add_cancel, zpow_zero]
  · apply GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb
    show ‖S.E.iK _‖ = 1
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, map_inv₀, map_inv₀, hrm, hrb, Formalism.L2.Ker.lamC_mul S.lam (inv_mem hmQ) (inv_mem (zpow_mem hQ _)),
      lamC_inv S.lam hmQ, lamC_inv S.lam (zpow_mem hQ _), lamC_zpow S.lam hQ,
      norm_mul, norm_mul, norm_inv, norm_inv, norm_zpow, norm_zpow, hnorm, hone, one_zpow, inv_one, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ hpK)]
  · show S.E.iK _ = _
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, hrm, hra]
  · show S.E.iK _ = _
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, map_inv₀, map_inv₀, hrm, hrb, zpow_neg (chiI J π)]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoUnitsAtPlaceUniformizingIdeleStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.two_units_at_place_uniformizing_idele : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => KIn t → S.Pos → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, (sysS H X std).Lv.comp j → (sysS H X std).Lv.comp (j + 1) → ∃ a b : (sysS H X std).G.Kf, (sysS H X std).vEqK a 0 ∧ (sysS H X std).vEqK b 0 ∧ S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) ∧ S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))))) := by
  first | exact @GlobalTheory.TwV.Xc.two_units | exact GlobalTheory.TwV.Xc.two_units | (intros; apply GlobalTheory.TwV.Xc.two_units <;> assumption)
end
end
