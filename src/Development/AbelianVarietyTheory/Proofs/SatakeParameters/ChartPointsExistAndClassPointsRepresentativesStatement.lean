module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartLevelBaseFrameCongrOneAtBadPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveIntegralRightTranslateStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointLeftTranslateRationalUnitaryStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalConditionInvariantRightLevelTranslate

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory



theorem funMoved_mul_level : ∀ {D : Formalism.BasicNotions.D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : lev.U) (d : Deco X.E (D.R.N i) ST SG), FunMoved s lev P v h ι y d → FunMoved s lev P v h ι (y * κ.1) d := by
  intro D X s i hi T bad lev ST SG P v h ι x κ d
  unfold FunMoved
  intro H w hw z hz
  have hU := (lev.U_eq κ.1).1 κ.2
  have hk : bc (prV (E := D.host.E) v) κ.1 ∈ lev.Uloc v := hU.2 v
  rw [lev.UlocAlt v h] at hk
  have hk2 := (Subgroup.mem_inf.1 hk).2
  change ∃ _, _ at hk2
  obtain ⟨hst, hf⟩ := hk2
  have hp : pullV (F := D.host.F) (x * κ.1) (fun a => s.iE (w a)) =
      (κ.1⁻¹).val *ᵥ pullV (F := D.host.F) x (fun a => s.iE (w a)) := by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  have hz1 : z.1 = (bc (prV (E := D.host.E) v) κ.1⁻¹).val *ᵥ
      (fun l => prV (E := D.host.E) v (pullV (F := D.host.F) x (fun a => s.iE (w a)) l)) := by
    rw [hz, hp]
    funext l
    exact RingHom.map_mulVec _ _ _ l
  have hz0 : (bc (prV (E := D.host.E) v) κ.1).val *ᵥ z.1 =
      fun l => prV (E := D.host.E) v (pullV (F := D.host.F) x (fun a => s.iE (w a)) l) := by
    have e : (bc (prV (E := D.host.E) v) κ.1).val * (bc (prV (E := D.host.E) v) κ.1⁻¹).val = 1 := by
      rw [← Units.val_mul (bc (prV (E := D.host.E) v) κ.1), ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    refine (congrArg (fun y => (bc (prV (E := D.host.E) v) κ.1).val *ᵥ y) hz1).trans ?_
    simp only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  rw [H w hw ⟨_, (hst z.1).1 z.2⟩ hz0]
  exact congrArg ι (hf z)

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalConditionInvariantRightLevelTranslateStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.functionalCondition_invariant_rightLevelTranslate : ∀ {D : Formalism.BasicNotions.D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : lev.U) (d : Deco X.E (D.R.N i) ST SG), FunMoved s lev P v h ι y d → FunMoved s lev P v h ι (y * κ.1) d := by
  first | exact @GlobalTheory.funMoved_mul_level | exact GlobalTheory.funMoved_mul_level | (intros; apply GlobalTheory.funMoved_mul_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointRightTranslateByChartLevel

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Hat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem levU_mulVec_mem_hatL (S : StepLevel F E σ J T f bad) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ S.U)
    (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb) :
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb := by
  refine Formalism.L2.Geo.Def.PN.latS_of_loc S.Lb S.Lb_span _ fun v => ?_
  have h1 := Formalism.L2.Geo.Def.PN.prV_latS S.Lb v hz
  have h2 : bc (prV (E := E) v) g ∈ levelVL σ J v S.Lb := S.Uloc_lev v (((S.U_eq g).1 hg).2 v)
  have h3 := (h2.2 _).1 h1
  have e : (fun i => prV (E := E) v (((g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) i)) =
      ((bc (prV (E := E) v) g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
        fun i => prV (E := E) v (z i) := by
    funext i
    exact RingHom.map_mulVec (prV (E := E) v) (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) z i
  rw [e]
  exact h3

theorem hatStab_of_levU (S : StepLevel F E σ J T f bad) (κ : S.U) : HatStab S.Lb κ.1 := by
  intro z
  constructor
  · intro hz
    have := levU_mulVec_mem_hatL S κ.1 κ.2 _ hz
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  · intro hz
    exact levU_mulVec_mem_hatL S κ.1⁻¹ (S.U.inv_mem κ.2) z hz

end Hat

theorem isPtAd_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H i hi β x x' p κ hx hp
  obtain ⟨p', hN, hf, hfr⟩ := GlobalTheory.T.chartPoint_frames_move_integralRightTranslate A dtU a hP H i p
    (fun P => ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P))
    (fun P => (ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))
    (GlobalTheory.T.chartLevel_baseFrame_congr_one_at_badPrime A dtU a hP H i hi β x p κ hp) hp.frame
  refine ⟨p', ⟨?_, ?_, ?_⟩⟩
  · rw [hN, hp.lat]
    unfold latCo
    rw [hx, latAd_stab _ _ _ (hatStab_of_levU _ κ)]
  · intro P
    have e : ratA D.host.F (A.crd i hi) * x'.1 * ratA D.host.F (A.fb i hi β P) =
        ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P) *
          ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) := by
      rw [hx]; simp only [mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact hfr P
  · intro P v h hv
    have e : ratA D.host.F (A.crd i hi) * x'.1 = ratA D.host.F (A.crd i hi) * x.1 * κ.1 := by
      rw [hx, mul_assoc]
    have h1 := GlobalTheory.T.functionalCondition_invariant_rightLevelTranslate t.seam _ P v h (iotaOf A i hi β P v h) _ κ _ (hp.fnl P v h hv)
    rw [e]
    intro w hw z hz
    have h2 := h1 w (by rw [← hN]; exact hw) z hz
    exact (congrFun (congrFun hf P) w).trans h2

end GlobalTheory.TwV

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointRightTranslateByChartLevelStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.chartBasePoint_rightTranslate_by_chartLevel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  first | exact @GlobalTheory.TwV.isPtAd_mul_lev | exact GlobalTheory.TwV.isPtAd_mul_lev | (intros; apply GlobalTheory.TwV.isPtAd_mul_lev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsExistAndClassPointsRepresentatives

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cls

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

theorem isPtAd_cls (H : AdTie A dtU a) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.chTw u μ).cls i) :
    IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) := by
  refine ⟨?_, H.frame i hi c, ?_⟩
  · rw [← H.N_eq i hi c]
    exact H.lat i hi c
  · intro P v h hv
    exact Classical.epsilon_spec (H.fnl i hi ((St i hi).chOf c) P v h hv) c rfl

theorem exists_cls_eq (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) :
    ∃ c : (D.chTw u μ).cls i, (St i hi).chOf c = β ∧ ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi),
      ∃ κ : ((St i hi).K β).lev.U, x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 := by
  obtain ⟨⟨c, rfl⟩, hc⟩ := ((St i hi).K β).y_bij.2 (Quotient.mk'' x)
  obtain ⟨g, hg, k, hk, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hc
  rw [Subgroup.mem_subgroupOf] at hg hk
  obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.1 hg
  refine ⟨c, rfl, γ, hγ, ⟨k.1, hk⟩, ?_⟩
  have e1 := congrArg Subtype.val e
  simp only [Subgroup.coe_mul] at e1
  rw [e1, ← hγg]
  rfl

end Cls

theorem ptEx_of_tie (hR : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p')) (hL : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p')) : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie
  have hcls : ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) :=
    fun i hi c => isPtAd_cls hTie i hi c
  refine ⟨fun i hi β x => ?_, hcls⟩
  obtain ⟨c, hcβ, γ, hγ, κ, hx⟩ := exists_cls_eq (St := St) i hi β x
  subst hcβ

  let k : UA D i hi := ⟨κ.1, (((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2 |>.1⟩

  let x₁ : UA D i hi := x * k⁻¹
  have hx₁ : x₁.1 = ratA D.host.F γ * ((St i hi).y c).1 := by
    show x.1 * (κ.1)⁻¹ = _
    rw [hx, mul_inv_cancel_right]
  obtain ⟨p₁, hp₁⟩ := hR A dtU a hPin hTie i hi _ ((St i hi).y c) x₁ (A.pt i hi c) γ hγ hx₁ (hcls i hi c)
  have hxk : x.1 = x₁.1 * κ.1 := by
    show x.1 = x.1 * (κ.1)⁻¹ * κ.1
    rw [inv_mul_cancel_right]
  exact hL A dtU a hPin hTie i hi _ x₁ x p₁ κ hxk hp₁

theorem ptEx_isPtAd : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) :=
  ptEx_of_tie GlobalTheory.T.chartPoint_leftTranslate_rationalUnitary GlobalTheory.T.chartBasePoint_rightTranslate_by_chartLevel

end GlobalTheory.TwV
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsExistAndClassPointsRepresentativesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.chartPoints_exist_and_classPoints_representatives : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) := by
  first | exact @GlobalTheory.TwV.ptEx_isPtAd | exact GlobalTheory.TwV.ptEx_isPtAd | (intros; apply GlobalTheory.TwV.ptEx_isPtAd <;> assumption)
end
end
