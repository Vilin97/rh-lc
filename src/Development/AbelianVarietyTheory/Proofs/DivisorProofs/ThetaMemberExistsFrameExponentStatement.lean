module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelKilledCharOfTorusLabelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigTorsFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsDividingGroupLabelStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjectiveClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberLiesOverRescaleFrames

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep

theorem over_rescale : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (e e' : FrAt x) (l : FractionRing V), l ≠ 0 → (∀ z J, Good 𝔪.A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val) → (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z l * (val w' (𝟙 _) z J).val) → 𝔪.Over' w₀ g w x e → 𝔪.Over' w₀ g w' x e' := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ g w w' x e e' l hl he hw H k hk wk' hwk' hgen s s' v hs hv
  have hlk : l ^ k ≠ 0 := pow_ne_zero k hl
  obtain ⟨wk, hwkg, hwk⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale wk' hgen hlk
  have h₁ : ValAt s x e (l ^ k * v) := fun z J hJ => by
    rw [hv z J hJ]
    have r₁ : Geo.Tor.val (powFrame 𝔪.A.A 𝔪.A.L x e (k : ℤ)) (𝟙 _) z J = Geo.Tor.val e (𝟙 _) z J ^ (k : ℤ) :=
      map_zpow _ _ _
    have r₂ : Geo.Tor.val (powFrame 𝔪.A.A 𝔪.A.L x e' (k : ℤ)) (𝟙 _) z J = Geo.Tor.val e' (𝟙 _) z J ^ (k : ℤ) :=
      map_zpow _ _ _
    rw [r₁, r₂, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    simp only [id, GlobalTheory.Poinc.TorsRatio.cst_eq_cstK, map_mul, map_pow]
    ring
  have h₂ := H k hk wk (fun z J hJ => Units.ext (by
    rw [hwk z J hJ, hwk' z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hw z J hJ, mul_pow,
      GlobalTheory.UT.CoefBasic.cst_eq, map_pow])) hwkg s s' _ hs h₁
  have h₃ := GlobalTheory.Poinc.Sep.sumF_const_mul (l ^ k)⁻¹ h₂
  simpa only [GlobalTheory.UT.TorsionValue.coef_scale hgen hwk, inv_mul_cancel_left₀ hlk] using h₃

end GlobalTheory.GSep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberLiesOverRescaleFramesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

theorem _root_.GlobalTheory.T.thetaMember_lies_over_rescale_frames : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (e e' : FrAt x) (l : FractionRing V), l ≠ 0 → (∀ z J, Good 𝔪.A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val) → (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z l * (val w' (𝟙 _) z J).val) → 𝔪.Over' w₀ g w x e → 𝔪.Over' w₀ g w' x e' := by
  first | exact @GlobalTheory.GSep.over_rescale | exact GlobalTheory.GSep.over_rescale | (intros; apply GlobalTheory.GSep.over_rescale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusCharacterUnique

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.GSep.TorCharUnique


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem equiv_of_qkToAkU {R : Type} [CommRing R] [IsDomain R] {J : Ideal R} (hB : AdmBase R J) {D : DegData R J}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (U : Unif J D A G) {k : ℕ} (hk : 1 ≤ k) (p p' : QkPt D.toPre (FractionRing R) k)
    (x : TFK (R := R) (FractionRing R) ⟶ A.A) (h : QkToAkU U.toUnifPre (FractionRing R) k p x)
    (h' : QkToAkU U.toUnifPre (FractionRing R) k p' x) : QkPt.Equiv D.toPre (FractionRing R) p p' := by
  have hL : Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  let F := AlgebraicClosure (FractionRing R)
  have hf : (algebraMap (FractionRing R) F).comp (algebraMap (FractionRing R) (FractionRing R)) =
      algebraMap (FractionRing R) F := RingHom.ext fun _ => rfl
  refine (GlobalTheory.ArcExt.equiv_qkExt_iff (algebraMap (FractionRing R) F) hf D.tau_bimult p p').1 ?_
  refine GlobalTheory.TorsionMapInj.qkToAk_injective_closed R J hB D A G hG U F k hk _ _
    (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x) ?_ ?_
  · exact (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.globalFns hL.kerPow U hk
      ((GlobalTheory.TorusExt.qkExt_iff D.tau_bimult _ hf p _).2 rfl) x).1 h
  · exact (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.globalFns hL.kerPow U hk
      ((GlobalTheory.TorusExt.qkExt_iff D.tau_bimult _ hf p' _).2 rfl) x).1 h'



attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem torChar_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (τ : X₁.S.Gam) (χ χ' : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ → GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ' → χ = χ' := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 τ χ χ' h h'
  obtain ⟨p, x, hy, hg, hq, hx⟩ := h.2 _ ((isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ))
  obtain ⟨p', x', hy', hg', hq', hx'⟩ := h'.2 _ ((isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ'))
  obtain rfl : x = x' := by
    apply Over.OverMorphism.ext
    refine 𝔪.cart.1.hom_ext (hx.trans hx'.symm) ?_
    rw [Over.w, Over.w]
  have hB : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)
  obtain ⟨z, hz, he⟩ := (GlobalTheory.TorusExt.equiv_iff 𝔪.D.tau_bimult _ _).1
    (equiv_of_qkToAkU hB 𝔪.semi 𝔪.U hn p p' x hq hq')
  rw [hy, hy', zero_add] at hz
  have hz0 : z = 0 := by
    have : ((X₁.S.r * X₁.S.N : ℕ) : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hz.symm
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast (by omega))
  rw [hz0, map_zero, add_zero, hg, hg'] at he
  exact (Additive.ofMul.injective (GlobalTheory.TorusExt.torusPt_injective he)).symm

end GlobalTheory.GSep.TorCharUnique
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusCharacterUniqueStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

theorem _root_.GlobalTheory.T.thetaMember_torus_character_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (τ : X₁.S.Gam) (χ χ' : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ → GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ' → χ = χ' := by
  first | exact @GlobalTheory.GSep.TorCharUnique.torChar_unique | exact GlobalTheory.GSep.TorCharUnique.torChar_unique | (intros; apply GlobalTheory.GSep.TorCharUnique.torChar_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsFrameExponent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.FrameExpEx
open GlobalTheory.Poinc.TorsRatio

theorem torsFrame_ratio : ∀ (V : Type) [CommRing V] [IsDomain V] (A : PolAV (Sp (FractionRing V))) (ρA : LB.Gen (A.L.pull (eSec A.A))), ρA.IsGen → ∀ (N : ℕ), 1 ≤ N → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e e' : FrAt x), IsTorsFrame A ρA N x e → IsTorsFrame A ρA N x e' → ∃ l : FractionRing V, l ^ (N ^ 2) = 1 ∧ ∀ z J, Good A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val := by
  intro V _ _ A ρA _ N _ x e e' H H'
  obtain ⟨-, he, α, hα, nα, cα⟩ := H
  obtain ⟨-, he', α', hα', nα', cα'⟩ := H'
  obtain ⟨l, hl0, hl⟩ := frame_ratio he he'
  have hp : Function.Surjective A.A.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _ A.isAb).2
  have hαα : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) J, Good A.L z J →
      Geo.Tor.val α r z J = Geo.Tor.val α' r z J :=
    gen_unique A.isLB A.A.hom (eSec A.A) (Over.w η[A.A]) hp hα hα' (fun w I hI => by
      have a := val_corr hI nα (𝟙 _)
      have b := val_corr hI nα' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm)
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J hJ using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ : Good A.L z J := hJ
  have q : Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) = Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := by
    have a := val_corr hJ cα (𝟙 _)
    have b := val_corr hJ cα' (𝟙 _)
    have p₁ : Geo.Tor.val (powFrame A.A A.L x e ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    have p₂ : Geo.Tor.val (powFrame A.A A.L x e' ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_mul hJ, val_pull hJ] at a b
    rw [← p₁, ← p₂, a, b, hαα _ _ z J hJ]
  have hlN : l ^ (N ^ 2) = 1 := by
    have q' := congrArg Units.val q
    rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, hl z J hJ, mul_pow, ← map_pow] at q'
    have hu : IsUnit ((Geo.Tor.val e (𝟙 _) z J).val ^ (N ^ 2)) := (Units.isUnit _).pow _
    have h1 : cstK z (l ^ (N ^ 2)) = cstK z 1 := by
      rw [map_one]
      exact hu.mul_left_inj.1 (by rw [_root_.one_mul]; exact q'.symm)
    exact (cstK z).injective h1
  exact ⟨l, hlN, hl⟩

end GlobalTheory.GSep.FrameExpEx

namespace GlobalTheory.GSep.FrameExpEx
open GlobalTheory.GSep.TwistTranslate


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_frExp : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ), ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ e : ℕ, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e := by
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ t δ 𝔪 a ha τ hτ
  obtain ⟨T, hT⟩ := GlobalTheory.T.thetaMember_exists_terms_dividing_group_label I X₁ z₁ act x₀ hdiv V ev Y t δ 𝔪 a ha
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, -⟩ := hT
  obtain ⟨χ₀, hχ₀, hyp⟩ := GlobalTheory.T.exists_level_killed_char_of_torus_label I X₁ z₁ act V ev Y t δ 𝔪 τ hτ
  have hT₀ : GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ₀ := ⟨hχ₀, hyp⟩
  obtain ⟨ρA, hρA, htors⟩ := exists_rig_torsFrame 𝔪 x fr hx hfr
  have hg₀ : IsTor χ₀ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ₀)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' ()) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w₂, hw₂g, hw₂v⟩ : ∃ w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 (g' () + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)).b,
      w₂.IsGen ∧ ∀ z J, val w₂ (𝟙 _) z J = val (w ()) (𝟙 _) z J := by
    revert hb
    generalize (g' () + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)).b = b
    rintro rfl
    exact ⟨w (), (hc ()).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := over_translate 𝔪 w₀ hw₀ ρA hρA (x a) (fr a) (htors _)
    (g' ()) (w ()) (hc ()).1 (hc ()).2.1 (hc ()).2.2 χ₀ hχ₀ _ hg₀ p xτ hpy hpg hq _ hadd w₂ (fun z J _ => hw₂v z J)
    (x (a + τ)) (x_add 𝔪 x hx a τ xτ hxτ)
  have hN : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  obtain ⟨l, hl, hlv⟩ := torsFrame_ratio V 𝔪.A ρA hρA _ hN _ _ _ he₂ (htors (a + τ))
  obtain ⟨e, he⟩ := eq_yK_zeta_pow 𝔪 l hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hl
    exact zero_ne_one hl
  refine ⟨e, ⟨χ₀, hT₀⟩, x, fr, th, w₀, s, g' (), w (), hx, hfr, hth, hw₀, hs, (hc ()).1, (hc ()).2.1, (hc ()).2.2, ?_⟩
  intro χ hχ g₀ hg₀' g'' hadd'' w'' _ hval
  obtain rfl : χ₀ = χ := GlobalTheory.T.thetaMember_torus_character_unique I X₁ z₁ act V ev Y t δ 𝔪 τ χ₀ χ hT₀ hχ
  obtain rfl : g₀ = GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀) :=
    (GlobalTheory.TorusExt.isTorusPtF_iff_eq g₀ χ₀).1 ((isTor_iff _ _).1 hg₀')
  obtain rfl := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hadd''
  refine GlobalTheory.T.thetaMember_lies_over_rescale_frames I X₁ z₁ act V ev Y t δ 𝔪 w₀ _ w₂ w'' (x (a + τ)) e₂ (fr (a + τ)) l hl0 hlv (fun z J hJ => ?_) hov
  rw [hw₂v, hval z J hJ, he]

end GlobalTheory.GSep.FrameExpEx
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsFrameExponentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic


theorem _root_.GlobalTheory.T.thetaMember_exists_frame_exponent : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ), ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ e : ℕ, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e := by
  first | exact @GlobalTheory.GSep.FrameExpEx.exists_frExp | exact GlobalTheory.GSep.FrameExpEx.exists_frExp | (intros; apply GlobalTheory.GSep.FrameExpEx.exists_frExp <;> assumption)
end
end
