module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabMapCubical
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WitMove
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.RingTheory.RegularLocalRing.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWitOfPull

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WitnessMove

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}



theorem unif_move (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (t : SAB H (Sp R)) (m : SABMap t Y.t χ)
    (W' : ArcWit Y a I f u χ) (ψ : t.G ≅ W'.t.G)
    [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ W'.m.φ = m.φ) (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) :
    ∃ (bc : t.G ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W'.t.G) (D'' : Out.DegData R I)
      (hD : Out.IsPullDeg (RingHom.id R) W'.P.D.toPre D''.toPre) (U'' : Out.Unif I D'' W'.P.A t.G)
      (_ : Module (𝓞 E) D''.toPre.X) (oD : letI := H.starRing; D''.toPre.OAct (𝓞 E)),
      IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = ψ.hom.left ∧
      U''.LG = t.PP ∧
      U''.gen.hom.left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
        pullback.fst t.G.hom (Out.jK R) ≫ ψ.hom.left ∧
      Out.IsPullUnif (RingHom.id R) hD bc W'.P.U U'' ∧
      (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧
      (letI := H.starRing; ∀ x, oD.onB.act x ≫ hD.e.hom =
        hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.P.oD.onB.act x)) ∧
      (letI := H.starRing; U''.toUnifPre.OLinear (𝓞 E) oD W'.P.oA t.act.toRingAct) ∧
      (letI := H.starRing; TraceFormTwistIso D''.toPre oD H.w0) := by
  let _ := H.starRing
  have hs := specOf_id R
  have gp₁ : IsGrpPullback t.G W'.t.G (Out.specOf (RingHom.id R)) ψ.hom.left :=
    (isGrpPullback_of_iso ψ).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback W'.t.G (Out.specOf (RingHom.id R)))
  have gpG : IsGrpPullback W'.P.A.A W'.t.G (Out.jK R) (W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R)) := by
    have := W'.P.U.gen_hom
    have : IsMonHom W'.P.U.gen.symm.hom := by show IsMonHom W'.P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso W'.P.U.gen.symm).comp (isGrpPullback_pullback W'.t.G (Out.jK R))).congr
      (Category.id_comp _) rfl
  have gp₂ : IsGrpPullback ((Over.pullback (Out.jK R)).obj t.G) W'.t.G (Out.jK R)
      (pullback.fst t.G.hom (Out.jK R) ≫ ψ.hom.left) :=
    ((isGrpPullback_pullback t.G (Out.jK R)).comp (isGrpPullback_of_iso ψ)).congr (Category.comp_id _) rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp₂ gpG
  have hgi : W'.P.U.gen.inv.left ≫ W'.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (W'.P.A.L.pull eA.hom.left) (W'.P.U.LG.L.pull (pullback.fst t.G.hom (Out.jK R) ≫ bc.hom.left ≫
      pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := eA.hom.left ≫ W'.P.U.gen.inv.left)
      (chartPullSame W'.P.A.L (fun _ => eA.hom.left) (fun _ => W'.P.U.gen.hom.left) _ _ fun _ => by
        rw [Category.assoc, hgi, Category.comp_id])
      (chartPullSame W'.P.U.LG.L _ (fun _ => pullback.fst W'.t.G.hom (Out.jK R)) _ _ fun _ => by
        rw [hbc, ← heA]; simp only [Category.assoc]) W'.P.U.ext
  obtain ⟨wL', he', gL, rL⟩ := rigIso_congr W'.P.bundle (CubeMap.ofHom ψ.hom) (sabMap_cubical m W'.m ψ hφ) hbc
    (e := Out.specOf (RingHom.id R)) hs
  obtain ⟨Wo, hWo, hψW⟩ := h5.psiOnExists R I hR W'.P.D
  have hgen : (Out.specOf (RingHom.id R)).base (genericPoint (Spec (CommRingCat.of R))) ∈ Wo := by
    rw [hs]; exact hWo
  have hI : I.map (RingHom.id R) ≤ I := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', hLG, hgenU, hPU⟩ := hU R R I I hR hR (RingHom.id R) hI W'.P.D W'.P.A W'.t.G W'.t.semi W'.P.U
    Wo hψW hgen t.G bc mbc W'.P.A rfl eA mE wA t.PP wL' he' gL rL
  have hbcact : ∀ x, t.act.toRingAct.act x ≫ bc.hom =
      bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.toRingAct.act x) := by
    intro x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫
          pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = pullback.fst _ _ ≫ (W'.t.act.act x).left :=
        pullback.lift_fst _ _ _
      show (t.act.act x ≫ bc.hom).left ≫ _ =
        (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, hbc, ← Category.assoc, hbc,
        ← Over.comp_left, hact, Over.comp_left]
    · exact (Over.w (t.act.act x ≫ bc.hom)).trans
        (Over.w (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x))).symm
  have actA : ∀ x, (W'.P.oA.act x).left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
      W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) ≫ (W'.t.act.act x).left := by
    intro x
    have e : W'.P.oA.act x ≫ W'.P.U.gen.inv = W'.P.U.gen.inv ≫ (Over.pullback (Out.jK R)).map (W'.t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (W'.P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (Out.jK R)).map (t.act.toRingAct.act x) ≫ U''.gen.hom =
      U''.gen.hom ≫ W'.P.oA.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply gpG.1.hom_ext
    · have a₁ : ((Over.pullback (Out.jK R)).map (t.act.act x)).left ≫ pullback.fst t.G.hom (Out.jK R) =
          pullback.fst t.G.hom (Out.jK R) ≫ (t.act.act x).left := pullback.lift_fst _ _ _
      have a₃ : (t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (W'.t.act.act x).left := by
        rw [← Over.comp_left, hact, Over.comp_left]
      show ((Over.pullback (Out.jK R)).map (t.act.act x) ≫ eA.hom).left ≫ _ = (eA.hom ≫ W'.P.oA.act x).left ≫ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₃, Over.comp_left,
        Category.assoc, actA, reassoc_of% heA]
    · rw [Over.w, Over.w]
  obtain ⟨mod'', oD'', xl, el, lin'', w0''⟩ := h5.oLinBaseChange R R I I hR hR (RingHom.id R) W'.P.D W'.P.A W'.t.G W'.P.U
    t.G bc mbc W'.P.A D'' hD U'' hPU (𝓞 E) W'.P.oD W'.P.oA W'.t.act.toRingAct W'.P.lin t.act.toRingAct hbcact
    W'.P.oA extA
  refine ⟨bc, D'', hD, U'', mod'', oD'', mbc, hbc, hLG, ?_, hPU, xl, el, lin'', w0'' H.w0 W'.P.w0⟩
  rw [hgenU]; exact heA



theorem exists_wit_of_pull (h5 : Out.Laws5) (hQ : QkPullExistsSt) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) (t : SAB H (Sp R))
    (m : SABMap t Y.t χ) (P : PELUnif I t)
    (bc : t.G ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W.t.G) [IsMonHom bc.hom]
    (hbc : bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf (RingHom.id R)) ≫ W.m.φ = m.φ)
    (hD : Out.IsPullDeg (RingHom.id R) W.P.D.toPre P.D.toPre) (hPU : Out.IsPullUnif (RingHom.id R) hD bc W.P.U P.U)
    (xl : ∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y)
    (el : letI := H.starRing; ∀ x, P.oD.onB.act x ≫ hD.e.hom =
      hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W.P.oD.onB.act x)) :
    ∃ W' : ArcWit Y a I f u χ, W'.t = t ∧ HEq W'.m m ∧ HEq W'.P P := by
  letI := H.starRing
  obtain ⟨he, w, e, -, -, d1, d2, d3, d4, d5, d6⟩ := ArcWit.witMove h5 hQ hR W P.U P.oD bc hD hPU xl el
  refine ⟨⟨t, m, P, _, he, w, e, d1, d2, d3, d4, d5, fun F _ _ _ _ uF h1 h2 => ⟨(d6 F uF h1 h2).1,
    fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => (d6 F uF h1 h2).2 yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 ?_⟩⟩,
    rfl, HEq.rfl, HEq.rfl⟩
  rw [hbc]; exact e4



theorem exists_wit (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5) (h6 : Out.UnifUniqSt) (hQ : QkPullExistsSt)
    {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type}
    [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} (hR : Out.AdmBase R I) {f : O' →+* R} {u : R}
    {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t) :
    ∃ W' : ArcWit Y a I f u χ, W'.t = t ∧ HEq W'.m m ∧ HEq W'.P P := by
  letI := H.starRing
  have hs := specOf_id R
  obtain ⟨ψ, hψ, hφ, hact, -⟩ := sabMap_iso m W.m rfl rfl
  obtain ⟨bc, D'', hD₂, U'', mod'', oD'', mbc, hbc, hLG, -, hPU₂, xl₂, el₂, lin'', w0''⟩ :=
    unif_move hU h5 hR t m W ψ hφ hact
  let P'' : PELUnif I t :=
    { D := D'', mod := mod'', oD := oD'', A := W.P.A, oA := W.P.oA, U := U'', bundle := hLG, lin := lin'', w0 := w0'' }
  obtain ⟨⟨t₁, m₁, P₁, φ₁, he₁, w₁, e₁, s₁⟩, rfl, hm₁, hP₁⟩ := exists_wit_of_pull h5 hQ hR W t m P'' bc
    (by rw [reassoc_of% hbc, hφ]) hD₂ hPU₂ xl₂ el₂
  obtain rfl : m₁ = m := eq_of_heq hm₁
  clear hP₁
  have res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U)
      (x : Γ(X, U)ˣ) : res h (res h' x) = res (h.trans h') x := by
    have e : X.presheaf.map (homOfLE h').op ≫ X.presheaf.map (homOfLE h).op =
        X.presheaf.map (homOfLE (h.trans h')).op := by
      rw [← Functor.map_comp]
      rfl
    apply Units.ext
    exact congrArg (fun φ => φ.hom (x : Γ(X, U))) e

  have res_g_mul_res_g_eq_res_g_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
      (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
      res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
    have hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
    have key := congrArg (⇑(res hW)) (hL.cocycle i j k)
    simp only [map_mul, res_res_lemma] at key
    exact key

  have isGen_g_iso_self_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
      (⟨fun p : L.ι × L.ι => L.g p.1 p.2⟩ : LB.Iso L L).IsGen := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
    have h₀ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U p₂ := inf_le_left
    have h₁ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₁ :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    have h₂ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U q₁ ⊓ L.U q₂ := inf_le_right
    have h₃ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₂ :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
    have h₄ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₂ ⊓ L.U q₂ :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    have c₁ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ q₁ q₂ h₁ h₂ h₃
    have c₂ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ p₂ q₂ h₀ h₄ h₃
    have key : res h₀ (L.g p₁ p₂) =
        res h₁ (L.g p₁ q₁) * (res h₄ (L.g p₂ q₂))⁻¹ * res h₂ (L.g q₁ q₂) := by
      rw [mul_right_comm, c₁, ← c₂, mul_inv_cancel_right]
    exact key

  have exists_iso_pair_of_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G}
      (h : L₁ = L₂) :
      ∃ (w : LB.Iso L₁.L L₂.L) (w' : LB.Iso L₂.L L₁.L), w.IsGen ∧ w'.IsGen ∧
        LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig ∧
        LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₂.rig L₁.rig := by
    cases h
    refine ⟨⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩, ⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩,
      isGen_g_iso_self_of_isLB L₁.isLB, isGen_g_iso_self_of_isLB L₁.isLB, ?_, ?_⟩
    · intro p
      exact L₁.rigGen p.1 p.2
    · intro p
      exact L₁.rigGen p.1 p.2
  obtain ⟨wL₀, -, g₀, -, m₀, -⟩ := exists_iso_pair_of_eq (P.bundle.trans P₁.bundle.symm)
  obtain ⟨hD₁, hlev, holin⟩ := h6 R I hR P₁.D P.D P₁.A P.A t₁.G t₁.semi P₁.U P.U wL₀ g₀ m₀
  obtain ⟨xl₁, el₁⟩ := holin (𝓞 E) P₁.oD P.oD P₁.oA P.oA t₁.act.toRingAct P₁.lin P.lin
  have mR : IsMonHom (Iso.refl t₁.G).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨bc₀, mbc₀, hbc₀⟩ := grpPullback_iso ((isGrpPullback_of_iso (Iso.refl t₁.G)).congr hs.symm rfl)
    (isGrpPullback_pullback t₁.G (Out.specOf (RingHom.id R)))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst t₁.G.hom (Out.specOf (RingHom.id R)) = 𝟙 _ := hbc₀
  have hPU₁ := isPullUnif_of_uniq P₁.U P.U hD₁ wL₀ g₀ m₀ hlev bc₀ hbc₀'
  exact exists_wit_of_pull h5 hQ hR ⟨t₁, m₁, P₁, φ₁, he₁, w₁, e₁, s₁⟩ t₁ m₁ P bc₀
    (by rw [← Category.assoc]; exact (congrArg (· ≫ m₁.φ) hbc₀').trans (Category.id_comp _)) hD₁ hPU₁ xl₁ el₁

end GlobalTheory.WitnessMove
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataDescendsFromCompleteDVR

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ArcDataDescent



theorem hasArcData_descends : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ : Sp R ⟶ Y.X) (y : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → ∀ (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t), P.TorsionIso → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ g : R →+* V, Function.Injective g → I.map g ≤ IsLocalRing.maximalIdeal V → ¬ IsUnit (g u) → (∀ x, x ≠ 0 → IsUnit (g (f x))) → Y.HasArcData a (IsLocalRing.maximalIdeal V) (g.comp f) (g u) (spMap g ≫ χ) → Y.HasArcData a I f u χ := by
  intro hL h2 h3 h4 h5 h6 hH E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a R _ _ _ _ I f u hR _ hf χ y hy t m P hT V _ _ _ hV g hg hI
    _ _ hA
  letI := H.starRing
  obtain ⟨hV₁, hV₂, -⟩ := hV
  have hV : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV₂⟩
  have := hR.1
  have := hR.2.2.1
  obtain ⟨t', m₀, P', hD, bc, mbc, hPU, hm₀, xl, el⟩ :=
    exists_pelUnif_pull h3.cubePull hL.polBaseChange h4.unifBaseChange h5 hR hV t P g hg hI
  obtain ⟨m', hm'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₀
  obtain ⟨W₁⟩ := (Y.hasArcData_iff a _ _ _ _).1 hA
  obtain ⟨W, rfl, k₁, k₂⟩ := WitnessMove.exists_wit h4.unifBaseChange h5 h6.unifUniq (qkPullExists hL.globalFns) hV W₁
    t' m' P'
  obtain rfl : m' = W.m := (eq_of_heq k₁).symm
  obtain rfl : P' = W.P := (eq_of_heq k₂).symm
  have hm : W.m.φ = (bc.hom.left ≫ pullback.fst t.G.hom (specOf g)) ≫ m.φ := by rw [hm', hm₀]
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  have gD := pull_grp hD
  obtain ⟨φ, gφ, hφ, wφ⟩ := exists_desc_pol hL h2 hH f hg a.D₀.P P.D.toPre.P W.P.D.toPre.P gD s1 ⟨hD.w, hD.w_gen⟩
    ⟨W.w, s2⟩ (fun F _ _ i₁ i₂ => agree hL h2 h5 hR hV hf hg y hy m P hT W hD bc mbc hPU hm xl el F i₁ i₂)
  have he : eSec P.D.toPre.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A := (cubeMapOf gφ).e_comm
  obtain ⟨w, gw, rw'⟩ := Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap f) a.D₀.P.A P.D.toPre.P.A φ he
    ⟨a.D₀.P.L, a.D₀.rig, a.D₀.P.isLB, a.D₀.rig_gen⟩ ⟨P.D.toPre.P.L, P.D.toPre.rig, P.D.toPre.P.isLB, P.D.toPre.rig_gen⟩ wφ
  have pw := (isGen_iff w).1 gw
  have pD := (isGen_iff hD.w).1 hD.w_gen
  obtain ⟨w', T⟩ := exists_comp P.D.toPre.P.isLB w hD.w pw pD a.D₀.P.isLB W.P.D.toPre.P.isLB
  have tr : ∀ {F : Type} [Field F] {K : Type} [Fintype K] {pt : K → (Sp F ⟶ W.P.D.toPre.P.A.left)}
      {pt₀ : K → (Sp F ⟶ a.D₀.P.A.left)} {ε : K → ℤ} (s : LB.Gen (LB.LinComb W.P.D.toPre.P.L pt ε))
      (s₀ : LB.Gen (LB.LinComb a.D₀.P.L pt₀ ε)) (x : F), GenRel w' s s₀ x ↔ GenRel W.w s s₀ x := by
    have r₀ := (maps_iff w _ (fun _ => eSec a.D₀.P.A) _ P.D.toPre.rig a.D₀.rig (spMap f) _
      (rigPull_le φ (spMap f) he a.D₀.P.L) (fun _ => rfl)).1 rw'
    have r₂ := T.pmaps_comp P.D.toPre.P.isLB (fun _ => hD.he) r₀ (pmaps_rig' hD)
    rw [← spMap_comp] at r₂
    have g' := (isGen_iff w').2 (T.pgen_comp P.D.toPre.P.isLB pw pD)
    have key : ∀ (ψ : W.P.D.toPre.P.A.left ⟶ a.D₀.P.A.left) (v : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ψ)), ψ = W.φ →
        v.IsGen → PMaps v (K := PUnit) (fun _ => eSec W.P.D.toPre.P.A) (fun _ => eSec a.D₀.P.A) (fun _ => 1)
          W.P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) →
        ∀ {F : Type} [Field F] {K : Type} [Fintype K] {pt : K → (Sp F ⟶ W.P.D.toPre.P.A.left)}
          {pt₀ : K → (Sp F ⟶ a.D₀.P.A.left)} {ε : K → ℤ} (s : LB.Gen (LB.LinComb W.P.D.toPre.P.L pt ε))
          (s₀ : LB.Gen (LB.LinComb a.D₀.P.L pt₀ ε)) (x : F), GenRel v s s₀ x ↔ GenRel W.w s s₀ x := by
      rintro _ v rfl gv pv F _ K _ pt pt₀ ε s s₀ x
      rw [rigidified_iso_unique hL.globalFns W.P.D.toPre.P a.D₀.P.isLB W.φ v W.w gv s2 _ _
        ((maps_iff v _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) _
          (rigPull_le W.φ (spMap (g.comp f)) W.he a.D₀.P.L) (fun _ => rfl)).2 pv) s3]
    intro F _ K _ pt pt₀ ε s s₀ x
    exact key _ w' hφ g' r₂ s s₀ x
  let xD : W.P.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := xl }
  have := P.D.toPre.P.isAb.smooth
  have := a.D₀.P.isAb.proper
  let gam : FractionRing R →+* FractionRing V :=
    IsFractionRing.lift (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V _).comp hg)
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap V _ (g r) := fun r => IsFractionRing.lift_algebraMap _ r
  refine ⟨t, m, P, φ, he, w, W.e.trans xD, gφ, gw, rw', fun x => ?_, fun z => ?_, fun F _ _ _ _ uF ha hu => ?_⟩
  · refine ext_of_injective hg gD.1 a.D₀.P.A.hom ?_ ?_
    · rw [Category.assoc, gφ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, gφ.1.w]
    · rw [← Category.assoc, ← act_proj hD (el x), Category.assoc, hφ, s4 x, ← Category.assoc, hφ]
  · refine ext_of_injective (p := 𝟙 _) (p' := 𝟙 _) hg (IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans (Category.id_comp _).symm⟩) a.D₀.P.A.hom ?_ ?_
    · rw [Category.assoc, gφ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    · have k := hD.c_pr (W.e z)
      refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) k.symm)).trans ?_
      rw [Category.assoc, hφ, s5 z, spMap_comp, Category.assoc]
  · obtain ⟨F', _, _, σ, ρ, hσρ⟩ := exists_common_field (algebraMap (FractionRing R) F) gam
    letI : Algebra (FractionRing R) F' := (σ.comp (algebraMap (FractionRing R) F)).toAlgebra
    letI : Algebra (FractionRing O') F' := (σ.comp (algebraMap (FractionRing O') F)).toAlgebra
    letI : Algebra (FractionRing V) F' := ρ.toAlgebra
    have hF : ∀ r : R, algebraMap (FractionRing R) F' (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing V) F' (algebraMap V (FractionRing V) (g r)) := fun r =>
      (RingHom.congr_fun hσρ _).trans (congrArg ρ (hgam r))
    have ha' : ∀ x, algebraMap (FractionRing O') F' (algebraMap O' _ x) =
        algebraMap (FractionRing R) F' (algebraMap R _ (f x)) := fun x => congrArg σ (ha x)
    have hu' : σ uF = algebraMap (FractionRing R) F' (algebraMap R _ u) := congrArg σ hu
    have hj := jFK_comm hF
    have jR : jFK (R := R) F' = spMap σ ≫ jFK (R := R) F := spMap_comp _ _
    have jO : jFK (R := O') F' = spMap σ ≫ jFK (R := O') F := spMap_comp _ _
    refine ⟨fun z => ?_, fun yF hyF k p₀ s hs q₀ q x e₁ e₂ e₃ e₄ => ?_⟩
    · have k := (s6 F' (σ uF) (fun x => (ha' x).trans (hF _)) (hu'.trans (hF _))).1 z
      obtain ⟨n₁, n₂⟩ := pmaps_psi' hD hj (χ' := W.e z) rfl
      have k' := (genRel_transfer T P.D.toPre.P.isLB W.P.D.toPre.P.isLB (fun _ => n₁) n₂ _ _).2 ((tr _ _ _).2 k)
      rw [← map_zpow₀] at k'
      refine (genRel_pull_iff σ w _ _ _).1 ((genRel_congr P.D.toPre.P.isLB a.D₀.P.isLB w ?_ ?_
        (DVR.pullGen_isGen _ _ _ _ (P.D.toPre.psi_gen _) _)
        (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (P.D.toPre.psi_gen _) _) _)
        (DVR.pullGen_isGen _ _ _ _ (a.D₀.psi_gen _) _)
        (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (a.D₀.psi_gen _) _) _)
        (fun p J hJ => ?_) (fun p J hJ => ?_) _).1 k')
      · exact funext fun _ => (congrArg (· ≫ _) jR).trans (Category.assoc _ _ _)
      · exact funext fun _ => (congrArg (· ≫ _) jO).trans (Category.assoc _ _ _)
      · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_pull hJ _ _ _)).symm)
        exact congrArg (fun r => val (P.D.toPre.psi (hD.xe (W.e z))) r p J)
          ((congrArg (𝟙 _ ≫ ·) jR).trans (Category.assoc _ _ _).symm)
      · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_pull hJ _ _ _)).symm)
        exact congrArg (fun r => val (a.D₀.psi z) r p J) ((congrArg (𝟙 _ ≫ ·) jO).trans (Category.assoc _ _ _).symm)
    · have hk : 1 ≤ k := by
        rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact l.A_pos
        · exact le_trans (by norm_num) l.three_le
      obtain ⟨q₀', hq₀, -⟩ := TorusExt.existsUnique_qkExt a.bimult σ (F' := F') rfl q₀
      obtain ⟨q', hq, -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult σ (F' := F') rfl q
      let x' : TFK (R := R) F' ⟶ P.A.A := Over.homMk (spMap σ ≫ x.left) (by
        have w₂ : x.left ≫ P.A.A.hom = jFK (R := R) F := Over.w x
        show (spMap σ ≫ x.left) ≫ P.A.A.hom = jFK (R := R) F'
        rw [Category.assoc, w₂, jR])
      let σ' : F →ₐ[FractionRing R] F' := ⟨σ, fun _ => rfl⟩
      refine (TorsionExt.qkToAkU_iff_of_qkExt ⟨hL, h2, h3, h4, h5⟩ R I hR P.D P.A t.G t.semi P.U F F' σ' k hk q q' x x' hq
        rfl).2 ?_
      obtain ⟨τ, hτ, -⟩ := exists_qk_pull_equiv hL h2 R V g P.D.toPre W.P.D.toPre hD P.D.tau_bimult W.P.D.tau_bimult F' hF k
      obtain ⟨k₁, k₂⟩ := (hτ q' _).1 rfl
      refine toA_down hL hR hV m P W hD bc mbc hPU hm F' hF (σ uF) ha' hu' (spMap σ ≫ yF)
        (by rw [Category.assoc, hyF, jR, Category.assoc]) k p₀ s hs q₀' q' (τ q') x' (ArcSpecialise.qkExt_trans e₁ hq₀)
        k₁ k₂ ?_ (fun z => ?_) ?_
      · rw [k₁, AddEquiv.symm_apply_eq, hq.1, hq₀.1]; exact e₂
      · obtain ⟨n₁, n₂⟩ := pmaps_of_isPullGtF k₂ (χ' := W.e z) rfl
        refine (tr _ _ _).1 ((genRel_transfer T P.D.toPre.P.isLB W.P.D.toPre.P.isLB n₁ n₂ _ _).1 ?_)
        rw [← map_zpow₀, hq₀.1]
        exact (genRel_congr P.D.toPre.P.isLB a.D₀.P.isLB w (gtφ_ext rfl hq _) (gtφ_ext rfl hq₀ _) (q'.g.isGen _)
          (DVR.pullGen_isGen _ _ _ _ (q.g.isGen _) _) (q₀'.g.isGen _) (DVR.pullGen_isGen _ _ _ _ (q₀.g.isGen _) _)
          (fun p J hJ => val_corr hJ (hq.2.2 _) _) (fun p J hJ => val_corr hJ (hq₀.2.2 _) _) _).2
          ((genRel_pull_iff σ w _ _ _).2 (e₃ z))
      · show (spMap σ ≫ x.left) ≫ _ = _
        rw [Category.assoc, e₄, Category.assoc]

end GlobalTheory.ArcDataDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataDescendsFromCompleteDVRStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.arcData_descends_from_completeDVR : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ : Sp R ⟶ Y.X) (y : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → ∀ (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t), P.TorsionIso → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ g : R →+* V, Function.Injective g → I.map g ≤ IsLocalRing.maximalIdeal V → ¬ IsUnit (g u) → (∀ x, x ≠ 0 → IsUnit (g (f x))) → Y.HasArcData a (IsLocalRing.maximalIdeal V) (g.comp f) (g u) (spMap g ≫ χ) → Y.HasArcData a I f u χ := by
  first | exact @GlobalTheory.ArcDataDescent.hasArcData_descends | exact GlobalTheory.ArcDataDescent.hasArcData_descends | (intros; apply GlobalTheory.ArcDataDescent.hasArcData_descends <;> assumption)
end
end
