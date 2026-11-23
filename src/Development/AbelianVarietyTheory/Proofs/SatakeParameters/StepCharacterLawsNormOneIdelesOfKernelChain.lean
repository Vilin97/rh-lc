module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DeterminantCharacterUnitaryApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharactersAlgebraicUnitaryPointsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelStepCharacterEqOneIntegralUnitaryStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterCmInfinityType

section

@[expose] public section

noncomputable section

namespace GlobalTheory.KerJ.RatPts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Host NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.Mem.Chr (finPartI)

theorem isFin_finPart {L : Type} [Field L] [NumberField L] (a : Ideles L) : IsFinIdele (finPartI L a) := fun _ => rfl

end GlobalTheory.KerJ.RatPts

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host NumberField Classical Formalism.FrobeniusOrbits GlobalTheory.KerJ.RatPts

end GlobalTheory.KerJ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharacterNormOneEqInfinityType

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem mt_ratId : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧ ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 → ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 = ratId D.host.F D.host.E z → (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ i hi
  choose e he using fun τ => (D.hc τ).e_int ⟨i, hi⟩
  refine ⟨e, fun τ => (he τ).symm, fun z hz y hy => ?_⟩
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have hz' : (z : D.host.E) ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, hstar]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host ⟨z, hz'⟩
  simp only at hk
  let k' : t.X.Eˣ := Units.map t.seam.iE.symm.toRingHom.toMonoidHom k
  have hik : t.seam.iE (k' : t.X.E) = k := t.seam.iE.apply_symm_apply _
  have hq : A.q (ratId t.X.F t.X.E k') = dtU y := by
    apply hP.q_dt
    rw [hy]
    have hx : Units.map A.iA.toRingHom.toMonoidHom (ratId t.X.F t.X.E k') = ratId D.host.F D.host.E k := by
      apply Units.ext
      show A.iA ((k' : t.X.E) ⊗ₜ[t.X.F] 1) = (k : D.host.E) ⊗ₜ[D.host.F] 1
      rw [hP.iA_rat, hik]
    rw [hx, h90, MonoidHom.div_apply, MonoidHom.id_apply, eq_div_iff_mul_eq']
    apply Units.ext
    show ((z : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *
      (Formalism.UG.sigR (Formalism.L2.Forms.sigD D) _ ((k : D.host.E) ⊗ₜ[D.host.F] 1)) = (k : D.host.E) ⊗ₜ[D.host.F] 1
    rw [Formalism.UG.sigR]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have hs : Formalism.L2.Forms.sigD D (k : D.host.E) = D.host.conj k := bridge_star_holds D.R D.host _
    rw [hs, hk]
  have hmu : ((D.muTil (i + 1) (A.q (ratId t.X.F t.X.E k')) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ := by
    obtain ⟨ι, hι⟩ := exists_isAdIso t.X.F t.X.E
    rw [hP.muTil ι hι ⟨i, hi⟩ (GlobalTheory.Mem.Chr.finPartI _ (Neutral.B1.diagUnits _ k')) _ (GlobalTheory.KerJ.RatPts.isFin_finPart _)
      ((hι.1 (k' : t.X.E)).trans rfl), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag, Units.val_inv_eq_inv_val]
    obtain ⟨n, hn, hinf⟩ := (hP.mu0 ⟨i, hi⟩).inf
    rw [hinf k', ← Finset.prod_inv_distrib, ← t.seam.iT.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : n τ = 2 * -e (t.seam.iT τ) := by
      have h1 := hn τ
      simp only [he] at h1
      exact_mod_cast h1
    have hka : Formalism.L2.Col.Fields.embC t.X t.seam.σ₀ τ (k' : t.X.E) = TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) := by
      rw [← hik]; exact t.seam_ok.1 τ _
    have h1 := congrArg (TaylorLogMetric.embT D (t.seam.iT τ)) hk
    rw [map_mul] at h1
    rw [GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    rw [hka]
    have h0 : TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) ≠ 0 := by simp
    generalize TaylorLogMetric.embT D (t.seam.iT τ) (k : D.host.E) = a at *
    generalize TaylorLogMetric.embT D (t.seam.iT τ) (z : D.host.E) = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]
  have htw : (t.O u μ).mt (i + 1) (A.q (ratId t.X.F t.X.E k')) = D.muTil (i + 1) (A.q (ratId t.X.F t.X.E k')) := by
    by_cases h0 : μ = D.what₂.mu0
    · rw [(hP.ref h0).2]
    · obtain ⟨ξ, hξ, hmt⟩ := hP.tw μ h0 rfl
      rw [hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, hξ]
      have h1 : ((t.tup μ : Chr t.X.F t.X.E t.X.K)) (ratId t.X.F t.X.E k') = 1 := by
        have hm := (t.tup μ).2
        exact hm.1.1.1.1.1 ⟨k', rfl⟩
      rw [h1, map_one, mul_one]
  rw [← hq, htw, hmu]

end GlobalTheory.TwV

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharacterNormOneEqInfinityTypeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelChainCharacter_normOne_eq_infinityType : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧ ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 → ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 = ratId D.host.F D.host.E z → (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ) := by
  first | exact @GlobalTheory.TwV.mt_ratId | exact GlobalTheory.TwV.mt_ratId | (intros; apply GlobalTheory.TwV.mt_ratId <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChain

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.TwV.MuLawPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem generalLinearGroupOne_eq_of_det_eq {R : Type} [CommRing R] {g h : GL (Fin 1) R}
    (e : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h) : g = h := by
  have e' : ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) = ((Matrix.GeneralLinearGroup.det h : Rˣ) : R) := by rw [e]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one] at e'
  ext a b
  fin_cases a; fin_cases b
  exact e'

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def gl1 (x : (AfE F E)ˣ) : GL (Fin 1) (AfE F E) :=
  Units.map (Matrix.scalar (Fin 1) : AfE F E →+* Matrix (Fin 1) (Fin 1) (AfE F E)).toMonoidHom x

theorem det_ideleAsGL1 (x : (AfE F E)ˣ) : Matrix.GeneralLinearGroup.det (gl1 x) = x := by
  ext
  simp [gl1, Matrix.GeneralLinearGroup.val_det_apply]

theorem ideleAsGL1_mem_unitary_of_normOne (σ : E →ₐ[F] E) {x : (AfE F E)ˣ} (hx : x ∈ U1 σ) :
    gl1 x ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) := by
  have h1 : (x : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) = 1 := by
    have := congrArg (fun u : (AfE F E)ˣ => (u : AfE F E)) (MonoidHom.mem_ker.1 hx)
    simpa [conjId] using this
  show cT _ _ * _ * _ = _
  ext a b
  fin_cases a; fin_cases b
  simp [cT, gl1, Matrix.mul_apply, inclE]
  rw [← Algebra.TensorProduct.one_def, mul_one, mul_comm]; exact h1

end Gen

section D
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}
  (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt)

theorem muOf_det (j : ℕ) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    muOf t u μ dtU j (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt j (dtU y) : ℂˣ) : ℂ) := by
  have h : ∃ y' : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y'.1 = Matrix.GeneralLinearGroup.det y.1 := ⟨y, rfl⟩
  unfold muOf
  rw [dite_eq_left h]
  have e : h.choose = y := Subtype.ext (generalLinearGroupOne_eq_of_det_eq h.choose_spec)
  rw [e]

theorem exists_unitaryOne_det_eq_normOneIdele {x : (AfE D.host.F D.host.E)ˣ} (hx : x ∈ U1 (sigD D)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x :=
  ⟨⟨gl1 x, ideleAsGL1_mem_unitary_of_normOne _ hx⟩, det_ideleAsGL1 x⟩

end D

section D2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}
  (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt)



theorem muOf_det_mul (j : ℕ) (x y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    muOf t u μ dtU j (Matrix.GeneralLinearGroup.det x.1 * Matrix.GeneralLinearGroup.det y.1) =
      muOf t u μ dtU j (Matrix.GeneralLinearGroup.det x.1) * muOf t u μ dtU j (Matrix.GeneralLinearGroup.det y.1) := by
  have e : Matrix.GeneralLinearGroup.det x.1 * Matrix.GeneralLinearGroup.det y.1 =
      Matrix.GeneralLinearGroup.det (x * y).1 := by
    rw [Subgroup.coe_mul, map_mul]
  have h2 : dtU (x * y) = dtU x * dtU y := dtU.map_mul x y
  have h3 : (t.O u μ).mt j (dtU x * dtU y) = (t.O u μ).mt j (dtU x) * (t.O u μ).mt j (dtU y) :=
    ((t.O u μ).mt j).map_mul _ _
  have k1 := muOf_det (t := t) (u := u) (μ := μ) dtU j (x * y)
  rw [h2, h3, Units.val_mul, ← e] at k1
  rw [k1, muOf_det, muOf_det]

end D2

theorem rationalIdele_mem_normOne_of_norm_eq_one {D : D7} (z : D.host.Eˣ) (hz : (z : D.host.E) * D.host.conj (z : D.host.E) = 1) :
    ratId D.host.F D.host.E z ∈ U1 (sigD D) := by
  have hs : (sigD D : D.host.E →+* D.host.E) (z : D.host.E) = D.host.conj (z : D.host.E) := Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
  rw [U1, MonoidHom.mem_ker]
  ext
  simp only [MonoidHom.mul_apply, MonoidHom.id_apply, conjId, ratId, Units.val_mul, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]
  show inclE _ (z : D.host.E) * sigR (sigD D) _ (inclE _ (z : D.host.E)) = 1
  simp only [inclE, sigR, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [show (sigD D) (z : D.host.E) = D.host.conj (z : D.host.E) from hs, hz, Algebra.TensorProduct.one_def]

theorem muLaw_underTie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT'
  have hA := GlobalTheory.T.kernelChainCharacters_algebraic_unitaryPoints A dtU a hP hT'
  have hU := GlobalTheory.T.kernelStepCharacter_eq_one_integralUnitary A dtU a hP hT'
  have hR := GlobalTheory.T.kernelChainCharacter_normOne_eq_infinityType A dtU a hP hT'
  intro i hi
  refine ⟨fun y => muOf_det dtU (i + 1) y, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have h1 := muOf_det (t := t) (u := u) (μ := μ) dtU (i + 1) 1
    simp only [OneMemClass.coe_one, map_one, Units.val_one] at h1
    exact h1
  · intro x hx y hy
    obtain ⟨x', rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    obtain ⟨y', rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hy
    exact muOf_det_mul dtU (i + 1) x' y'
  · intro x hx
    obtain ⟨y, rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    rw [muOf_det]
    exact hA i hi y
  · intro x hx hint hv
    obtain ⟨y, rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    rw [muOf_det, hU i hi y hint hv, Units.val_one]
  · obtain ⟨e, he, hz⟩ := hR i hi
    refine ⟨e, he, fun z hz1 => ?_⟩
    obtain ⟨y, hy⟩ := exists_unitaryOne_det_eq_normOneIdele (rationalIdele_mem_normOne_of_norm_eq_one z hz1)
    rw [← hy, muOf_det]
    exact hz z hz1 y hy

end GlobalTheory.TwV.MuLawPf
end
end
end
