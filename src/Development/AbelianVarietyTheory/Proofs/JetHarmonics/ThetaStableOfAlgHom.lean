module

public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleMemSec
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelChangeActionOnCuspForms
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
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValuesInvariantUniversalEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueUnderLevelMove
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPointsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionShortThetaSeriesRootOfUnityMul

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelChangeActionOnCuspFormsStatement

section

@[expose] public section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_levelChangeAction_on_cuspForms : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)), ∃ act, IsLevAct T h j w ℓ act := by
  first | exact @GlobalTheory.FormTies.exists_isLevAct | exact GlobalTheory.FormTies.exists_isLevAct | (intros; apply GlobalTheory.FormTies.exists_isLevAct <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemThetaSeries

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaLevelMove

section Move

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.TranslMove GlobalTheory.VVRank GlobalTheory.ShortValMove
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_isVtOver {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {A : Over S'} [GrpObj A]
    [IsCommMonObj A] {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
    {T : Over S'} {T₀ : Over S} {τ : T.left ⟶ T₀.left} {L₀ : RigLB G} {L₁ : RigLB A}
    {w : LB.Iso L₁.L (L₀.L.pull φ)} (hw : w.IsGen)
    {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (h₁ : Ψ ≫ (fst T₀ G).left = (fst T A).left ≫ τ)
    (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)
    {e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left} (he : eSec A ≫ φ = e ≫ eSec G)
    (hρ : PMaps w (K := PUnit) (fun _ => eSec A) (fun _ => eSec G) (fun _ => 1) L₁.rig L₀.rig e) (N : ℕ)
    (hk : ∀ θ : ThetaGrp A L₁.L ((N : ℤ) ^ 2) T, θ.pt ^ (N ^ 2) = 1)
    {s₀ : LB.Sec (LPow G L₀.L 1 T₀)} {s : LB.Sec (LPow A L₁.L 1 T)} (hs : SecRel w Ψ s₀ s)
    {ok₀ : (T₀ ⟶ G) → Prop} {ok : (T ⟶ A) → Prop} {t₀ : T₀ ⟶ G} {t : T ⟶ A}
    (ht : ∀ y : T₀ ⟶ G, y ^ N = t₀ → ok₀ y → ∃ x : T ⟶ A, τ ≫ y.left = x.left ≫ φ ∧ x ^ N = t ∧ ok x)
    {F₀ : LB.Sec (LPow G L₀.L ((N : ℤ) ^ 2) T₀)} (H : IsVtOver G L₀ N ok₀ s₀ t₀ F₀) :
    ∃ F, IsVtOver A L₁ N ok s t F ∧ SecRel w Ψ F₀ F := by
  obtain ⟨y₁, β₀, β, r₁, V₁, hy, oy, g₀, n₀, cβ, tw, sl₁, ac₁⟩ := H
  obtain ⟨x₁, hx₁, hx, ox⟩ := ht y₁ hy oy
  obtain ⟨α₀, gα₀, nα₀, v₀⟩ := exists_normMul hp L₀.isLB L₁.isLB hw he hρ N g₀ n₀
  obtain ⟨α, gα, cα⟩ := NormMulUniv.exists_pull L₁.isLB α₀ gα₀ T
  have v : GenRel w Ψ β α := fun Z r z J₀ J hJ₀ hJ => by
    rw [val_corr hJ₀ cβ, val_pull hJ₀, val_corr hJ cα, val_pull hJ, Category.assoc, h₂, ← Category.assoc,
      v₀ Z _ z J₀ J hJ₀ hJ, Category.comp_id, Category.assoc, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨s₁, tw'⟩ := VVRank.exists_isTwistPull A (ψ := mulT A T N) (hm := lift_snd _ _) (b := 1) L₁.isLB gα s
  have R₁ := secRel_twist (lift_comm h₁ (pt_pow hp h₂ N) h₂) v tw tw' hs
  obtain ⟨U₁, l₁, a₁⟩ := exists_symLift hp L₀.isLB L₁.isLB hw h₁ h₂ hk hx₁ sl₁
  obtain ⟨F, b₁, R₂⟩ := a₁ _ _ _ ac₁ R₁
  exact ⟨F, ⟨x₁, α₀, α, s₁, U₁, hx, ox, gα₀, nα₀, cα, tw', l₁, b₁⟩, R₂⟩

theorem isVtOver_move (hLaw : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X}
    {ν : SABMap Xo.univ.t Xo.univ.t ρ} {x x' : Sp S ⟶ Xo.X} {pm : Gx x ⟶ Gx x'}
    {w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)}
    (h₁ : pm ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : pm ≫ (snd (Over.mk x') Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ) (hw : CubIso ν w)
    {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} (hs : SecRel (T := Over.mk x) (T₀ := Over.mk x') w pm s' s) (N : ℕ)
    {ok' : (ptO Xo x' ⟶ Xo.univ.t.G) → Prop} {ok : (ptO Xo x ⟶ Xo.univ.t.G) → Prop}
    {t' : ptO Xo x' ⟶ Xo.univ.t.G} {t : ptO Xo x ⟶ Xo.univ.t.G}
    (ht : ∀ q : ptO Xo x' ⟶ Xo.univ.t.G, q ^ N = t' → ok' q →
      ∃ p : ptO Xo x ⟶ Xo.univ.t.G, q.left = p.left ≫ ν.φ ∧ p ^ N = t ∧ ok p)
    {F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo x'))}
    (hF : IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok' s' t' F') :
    ∃ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo x)),
      IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F ∧ SecRel (T := ptO Xo x) (T₀ := ptO Xo x') w pm F' F := by
  have := UnivPol.isLocallyNoetherian Xo
  have hρ := (maps_iff w _ (fun _ => eSec Xo.univ.t.G) _ Xo.univ.t.PP.rig Xo.univ.t.PP.rig ν.cm.e _
    (rigPull_le ν.cm.F ν.cm.e ν.cm.e_comm Xo.univ.t.PP.L) (fun _ => rfl)).1 hw.2.1
  exact exists_isVtOver ν.cart (T := ptO Xo x) (T₀ := ptO Xo x') (τ := 𝟙 (Sp S)) hw.1
    (h₁.trans (Category.comp_id _).symm) h₂ ν.cm.e_comm hρ N
    (fun θ => pt_pow_eq_one hLaw.kerPow (UnivPol.pol Xo) (N ^ 2) (Nat.cast_pow N 2).symm θ) hs
    (fun q hq oq => (ht q hq oq).imp fun p hp => ⟨(Category.id_comp _).trans hp.1, hp.2⟩) hF

theorem nab_move (hLaw : Laws) (hCI : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {nab : NabV Xo c}
    (hnab : IsNab Xo c nab) {S : Type} [CommRing S] [Algebra c.F S] {ρ : Xo.X ⟶ Xo.X}
    {ν : SABMap Xo.univ.t Xo.univ.t ρ} {y y' : FrPt Xo c S} {pm : Gx y.x ⟶ Gx y'.x}
    {w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)} (hx : y'.x = y.x ≫ ρ)
    (h₁ : pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left)
    (h₂ : pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ) (hw : CubIso ν w)
    (hu : ∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (N : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)))
    (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x)))
    (hF : ∀ b, SecRel (T := ptO Xo y.x) (T₀ := ptO Xo y'.x) w pm (F' b) (F b)) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  have hL := Xo.univ.t.PP.isLB
  have e : (N : ℤ) ^ 2 = (N ^ 2 : ℕ) := (Nat.cast_pow N 2).symm
  refine GlobalTheory.T.harmonic_values_invariant_universal_endomorphism hLaw hCI E H Dw l Xo c nab hnab S ρ ν y y' pm w hx h₁ h₂ hw hu n a P hP N F F' fun b => ?_
  have hc := @secRel_iff _ _ _ _ _ _ ν.cm.F (ptO Xo y.x) (ptO Xo y'.x) _ _ w pm hL hL h₂ ((N : ℤ) ^ 2) (N ^ 2) e
  exact (hc _ _).1 (hF b)

theorem thValAt_move (hLaw : Laws) (hCI : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {nab : NabV Xo c}
    (hnab : IsNab Xo c nab) {S : Type} [CommRing S] [Algebra c.F S] {ρ : Xo.X ⟶ Xo.X}
    {ν : SABMap Xo.univ.t Xo.univ.t ρ} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La} {y y' : FrPt Xo c S}
    (hlev : IsLevMove ρ ν gM gA) (hmv : FrMove ρ ν y y') {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    {x : Fin n → Dw.La} {v : S} (hv : ThValAt Xo c nab y' x P v) :
    ThValAt Xo c nab y (fun b => gM (x b)) P v := by
  obtain ⟨S', _, _, φ, y₁', F', hff, hfr, hV, hval⟩ := hv
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.FramedBaseChange.exists_frMap hLaw E H Dw l Xo c S S' φ y
  obtain ⟨hx, hu, pm, ω, hf, hs, hω, hR⟩ := exists_move_baseChange hmv hy₁ hfr
  obtain ⟨e, he⟩ := exists_ptEquiv ν hx
  have he' : ∀ p, p.left = (e.symm p).left ≫ ν.φ := fun p => by rw [← he, e.apply_symm_apply]
  have hact : ∀ p b, e (p ≫ Xo.univ.t.act.act b) = e p ≫ Xo.univ.t.act.act b := fun p b =>
    Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, ν.act])
  have hact' : ∀ p b, e.symm p ≫ Xo.univ.t.act.act b = e.symm (p ≫ Xo.univ.t.act.act b) := fun p b =>
    e.injective (by rw [hact, e.apply_symm_apply, e.apply_symm_apply])
  have hlv : ∀ q : Dw.La, e (levPt Xo y₁.x (gM q)) = levPt Xo y₁'.x q := fun q => by
    refine Over.OverMorphism.ext ?_
    rw [he, levPt, levPt, Over.comp_left, Over.comp_left, Category.assoc, hlev.2.1, Over.toUnit_left,
      Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hx.symm)
  choose F hF hFF using fun b : Fin n =>
    isVtOver_move hLaw hf hs hω hR l.M (ok := KilledBy Xo (l.Mb ^ 2)) (t := levPt Xo y₁.x (gM (x b)))
      (fun p hp op => ⟨e.symm p, he' p, by rw [← map_pow, hp, ← hlv, e.symm_apply_apply],
        fun r hr => by rw [hact', op r hr, map_one]⟩) (hV b)
  refine ⟨S', inferInstance, inferInstance, φ, y₁, F, hff, hy₁, hF, ?_⟩
  rw [hval, thExpr, thExpr, nab_move hLaw hCI hnab hx hf hs hω hu hP l.M F F' hFF]

end Move

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem actLev_mem_th : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.th j w, f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.th j w := by
  intro hCI D T h j hj w γ f hf _
  obtain ⟨x, P, hP, hf⟩ := hf
  obtain ⟨st, hnab⟩ := h.nabPin j hj
  have hr : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
    have hk := D.R.m_add_three_le_k
    have h1 := hj.1
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  have hA := (GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hr h.pins.2.1.2).total
  refine ⟨fun b => liftLa γ (x b), P, hP, fun p y => ?_⟩
  obtain ⟨ρ, ν, -, hlev, hmv⟩ := mvPt_spec hA γ y
  exact thValAt_move GlobalTheory.firstFiveLaws.1 hCI hnab hlev hmv hP.1 (hf p _)

end GlobalTheory.ThetaLevelMove
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemThetaSeriesStatement

section

@[expose] public section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelAction_mem_thetaSeries : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.th j w, f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.th j w := by
  first | exact @GlobalTheory.ThetaLevelMove.actLev_mem_th | exact GlobalTheory.ThetaLevelMove.actLev_mem_th | (intros; apply GlobalTheory.ThetaLevelMove.actLev_mem_th <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionShortThetaSeriesRootOfUnityMulStatement

section

@[expose] public section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelAction_shortThetaSeries_rootOfUnity_mul : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ) (hj : InR D j), (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) → ∀ (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → ∀ (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.toTop.sh j w, ∃ (u : 𝓞 T.Q.c.F) (f' : T.R j), f' ∈ T.toTop.sh j w ∧ actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f = (u : T.Q.c.F) • f' := by
  first | exact @GlobalTheory.ShortMove.actLev_short | exact GlobalTheory.ShortMove.actLev_short | (intros; apply GlobalTheory.ShortMove.actLev_short <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaStableOfAlgHom

section

@[expose] public section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem theta_stable_of_algHom {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (Ψ : X.Forms →ₐ[B.KO] X.Forms) (Sc : WeightAlgebra.Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (hL : ∀ F ∈ X.thAll wL, ∃ F' ∈ X.thAll wL, Ψ (X.inc wL F) = X.inc wL F')
    (hS : ∀ w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) → ∀ F ∈ X.shortTh w, ∃ F' ∈ X.shortTh w, Ψ (X.inc w F) = X.inc w F') :
    ∀ x ∈ X.Theta Sc ka wL wF T, Ψ x ∈ X.Theta Sc ka wL wF T := by
  let Φ : X.Forms →ₐ[𝓞 B.KO] X.Forms := Ψ.restrictScalars _
  suffices key : (X.Theta Sc ka wL wF T).map Φ.toLinearMap ≤ X.Theta Sc ka wL wF T from
    fun x hx => key ⟨x, hx, rfl⟩
  change ∀ F ∈ X.thAll wL, ∃ F' ∈ X.thAll wL, Φ (X.inc wL F) = X.inc wL F' at hL
  change ∀ w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) → ∀ F ∈ X.shortTh w, ∃ F' ∈ X.shortTh w, Φ (X.inc w F) = X.inc w F' at hS
  have hsm : ∀ (s : 𝓞 B.KO) w (F : B.Cusp j w), X.inc w (s • F) = s • X.inc w F := fun s w F =>
    ((X.inc w).restrictScalars (𝓞 B.KO)).map_smul s F
  have hsc : ∀ (s : 𝓞 B.KO) w (N : Submodule (𝓞 B.KO) (B.Cusp j w)),
      (∀ F ∈ N, ∃ F' ∈ N, Φ (X.inc w F) = X.inc w F') →
      ∀ F ∈ X.scaled s w N, ∃ F' ∈ X.scaled s w N, Φ (X.inc w F) = X.inc w F' := by
    rintro s w N hN _ ⟨F, hF, rfl⟩
    obtain ⟨F', hF', e⟩ := hN F hF
    refine ⟨_, ⟨F', hF', rfl⟩, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, hsm, map_smul, e]
  have hemb : ∀ w (N : Submodule (𝓞 B.KO) (B.Cusp j w)),
      (∀ F ∈ N, ∃ F' ∈ N, Φ (X.inc w F) = X.inc w F') → (X.emb w N).map Φ.toLinearMap ≤ X.emb w N := by
    rintro w N hN _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    obtain ⟨F', hF', e⟩ := hN F hF
    exact ⟨F', hF', e.symm⟩
  have h1 : (X.emb wL (X.WWc Sc.sW wL)).map Φ.toLinearMap ≤ X.emb wL (X.WWc Sc.sW wL) :=
    hemb _ _ (hsc _ _ _ hL)
  have h2 : ∀ s w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) →
      (X.emb w (X.Thc s w)).map Φ.toLinearMap ≤ X.emb w (X.Thc s w) := fun s w hw =>
    hemb _ _ (hsc _ _ _ (hsc _ _ _ (hS w hw)))
  unfold WeightAlgebra.PJ.Theta
  rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_mul, Submodule.map_mul, Submodule.map_pow, Submodule.map_pow]
  refine sup_le_sup (sup_le_sup (mul_le_mul' (pow_le_pow_left' h1 _) (h2 _ _ (Or.inl rfl)))
    (mul_le_mul' (pow_le_pow_left' h1 _) (h2 _ _ (Or.inr (Or.inl rfl))))) (h2 _ _ (Or.inr (Or.inr rfl)))

theorem map_mem_spanIn {D : D7} {K : Type} [Field K] [NumberField K] {R : ℕ → Type} [∀ j, CommRing (R j)]
    [∀ j, Algebra K (R j)] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)]
    (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j)) (j : ℕ) (w : WeightFamilies.Wt D j) (s : Set (R j)) (ψ : R j →ₗ[K] R j)
    (hs : ∀ f ∈ s, ∃ (u : 𝓞 K) (f' : R j), f' ∈ s ∧ ψ f = (u : K) • f') (F F' : cutR C j w) (e : F'.1 = ψ F.1) (hF : F ∈ spanIn C j w s) :
    F' ∈ spanIn C j w s := by
  change F'.1 ∈ Submodule.span (𝓞 K) s
  rw [e]
  have hle : (Submodule.span (𝓞 K) s).map (ψ.restrictScalars (𝓞 K)) ≤ Submodule.span (𝓞 K) s := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨u, f', hf', e'⟩ := hs f hf
    have e'' : ψ f = u • f' := e'.trans (algebraMap_smul K u f')
    change ψ f ∈ Submodule.span (𝓞 K) s
    rw [e'']
    exact Submodule.smul_mem _ u (Submodule.subset_span hf')
  exact hle ⟨F.1, hF, rfl⟩

theorem coe_one_smul_eq {K : Type} [Field K] {R : ℕ → Type} [∀ j, CommRing (R j)] [∀ j, Algebra K (R j)] (j : ℕ)
    (x : R j) : x = ((1 : 𝓞 K) : K) • x := by
  simp

noncomputable def actLevAlg {D : D7} (T : Top D) (j : ℕ)
    (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l) : T.R j →ₐ[T.Q.c.F] T.R j :=
  AlgHom.ofLinearMap (actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ) rfl (fun _ _ => rfl)

theorem levAct_theta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Full D) (h : LawsP T.toTop) (j : ℕ) (hj : InR D j), LawsFull T → (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) → ∀ (Sc : WeightAlgebra.Scal (recB h.toLawsCore)) (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), WeightAlgebra.IsF' ka wL wF Tn wF.n → ka.n = wF.n + Tn * wL.n → WeightFamilies.dimY D j ≤ Tn → D.R.r ≤ wF.n → ∀ (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)) (act : P → (recB h.toLawsCore).Cusp j ka → (recB h.toLawsCore).Cusp j ka), IsLevAct T.toTop h j ka ℓ act → ∀ g F, (recPJ h j hj).inc ka F ∈ (recPJ h j hj).Theta Sc ka wL wF Tn → (recPJ h j hj).inc ka (act g F) ∈ (recPJ h j hj).Theta Sc ka wL wF Tn := by
  intro hC D T h j hj hfull hxi Sc ka wL wF Tn _ hn _ hr P ℓ act hact g F hF
  let ψ := actLevAlg T.toTop j (ℓ g)
  let Φ0 : AddMonoidAlgebra (T.R j) (Deg D j) →ₐ[T.Q.c.F] AddMonoidAlgebra (T.R j) (Deg D j) :=
    AddMonoidAlgebra.mapAlgHom (Deg D j) ψ
  let Φ : @AlgHom _ _ _ _ _ _ (recPJ h j hj).aF (recPJ h j hj).aF := Φ0
  have hΦ : ∀ w (F F' : (recB h.toLawsCore).Cusp j w), F'.1 = ψ F.1 →
      Φ ((recPJ h j hj).inc w F) = (recPJ h j hj).inc w F' := by
    intro w F F' e
    change Φ0 (AddMonoidAlgebra.single (deg w) F.1) = AddMonoidAlgebra.single (deg w) F'.1
    rw [e]
    exact AddMonoidAlgebra.mapAlgHom_single _ _ _
  have hspan : ∀ w (s : Set (T.R j)), (∀ f ∈ s, ∃ (u : 𝓞 T.Q.c.F) (f' : T.R j), f' ∈ s ∧ ψ f = (u : T.Q.c.F) • f') →
      ∀ F ∈ spanIn T.C j w s,
      ∃ F' ∈ spanIn T.C j w s, Φ ((recPJ h j hj).inc w F) = (recPJ h j hj).inc w F' := by
    intro w s hs F hF
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_levelChangeAction_on_cuspForms D T.toTop h j hj w P ℓ
    exact ⟨a g F, map_mem_spanIn T.C j w s ψ.toLinearMap hs F _ (ha g F) hF, hΦ w F _ (ha g F)⟩
  have hone : ∀ x : T.R j, x = ((1 : 𝓞 T.Q.c.F) : T.Q.c.F) • x := fun x => coe_one_smul_eq (R := T.R) j x
  have key := theta_stable_of_algHom (recPJ h j hj) Φ Sc ka wL wF Tn
    (hspan wL (T.th j wL) fun f hf => by
      obtain ⟨_, hnab⟩ := h.nabPin j hj
      exact ⟨1, ψ f, GlobalTheory.T.levelAction_mem_thetaSeries hC D T.toTop h j hj wL (ℓ g) f hf
        (GlobalTheory.thetaRule_mem_sec GlobalTheory.abelianSchemeLaws_all.1 hC _ _ _ _ _ _ _ hnab _ _ f hf), hone _⟩)
    (fun w hw => hspan w (T.toTop.sh j w) fun f hf => GlobalTheory.T.levelAction_shortThetaSeries_rootOfUnity_mul hC D T hfull j hj hxi w (by
      rcases hw with rfl | rfl | rfl
      · exact hr
      · exact hr.trans (Nat.le_add_right _ _)
      · rw [hn]; exact hr.trans (Nat.le_add_right _ _)) (ℓ g) f hf)
  rw [← hΦ ka F (act g F) (hact g F)]
  exact key _ hF

end GlobalTheory.FormTies
end
end
