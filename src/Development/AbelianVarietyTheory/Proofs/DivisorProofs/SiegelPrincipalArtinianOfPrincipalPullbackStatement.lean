module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCover
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfClosedProper

section

@[expose] public section

open GlobalTheory.AbLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SharpLift

theorem relAmple_of_closed_proper (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [IsProper B.hom] [Flat B.hom] (M : LB B.left) (hM : M.IsLB)
    (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀) (hg : Function.Surjective g)
    (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left)
    (hb : IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)))
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hA : RelAmple Y₀ N₀) : RelAmple B M := by
  have hker : RingHom.ker g ≤ RingHom.ker (IsLocalRing.residue R) := by
    rw [IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)
  let g' : R₀ →+* IsLocalRing.ResidueField R :=
    RingHom.liftOfSurjective g hg ⟨IsLocalRing.residue R, hker⟩
  have hg' : g'.comp g = IsLocalRing.residue R := RingHom.liftOfSurjective_comp g hg _
  let k := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hk : Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom g) = k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  let ψ : pullback B.hom k ⟶ Y₀.left := hb.lift (pullback.fst B.hom k)
    (pullback.snd B.hom k ≫ Spec.map (CommRingCat.ofHom g'))
    (by rw [Category.assoc, hk, pullback.condition])
  have hψ : ψ ≫ b = pullback.fst B.hom k := hb.lift_fst _ _ _
  have hψ' : IsPullback ψ (pullback.snd B.hom k) Y₀.hom (Spec.map (CommRingCat.ofHom g')) := by
    refine IsPullback.of_right ?_ (hb.lift_snd _ _ _) hb
    rw [hψ, hk]
    exact IsPullback.of_hasPullback _ _
  have h₁ : RelAmple ((Over.pullback k).obj B) (M.pull (pullback.fst B.hom k)) :=
    GlobalTheory.AmpleLocalBase.relAmple_baseChange (A' := (Over.pullback k).obj B) hψ' hN₀ (pull_isLB hM _)
      (LBIso.chartPull (Geo.Tor.chartPullPull N₀ ψ ψ rfl)
        (chartPullSame M (fun _ : PUnit => pullback.fst B.hom k) (fun _ => b) (fun _ => 1) ψ
          fun _ => hψ.symm) hiso).symm hA
  obtain ⟨r, hr, h₂⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hM (IsLocalRing.residue R) (fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨a, 1, by simp, by simp⟩) h₁
  have hu : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).1 hr
  have htop : PrimeSpectrum.basicOpen r = ⊤ := by
    exact top_le_iff.1 fun p _ => fun hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  generalize (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens) = U at htop h₂
  subst htop
  let j := Scheme.Opens.ι (X := Spec (CommRingCat.of R)) ⊤
  have : IsIso j := inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
  have : IsAffine (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme := isAffineOpen_top _
  have h₃ : IsPullback (inv (pullback.fst B.hom j)) B.hom (pullback.snd B.hom j) (inv j) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]⟩
  refine GlobalTheory.AmpleLocalBase.relAmple_baseChange (A := (Over.pullback j).obj B) h₃ (pull_isLB hM _) hM ?_ h₂
  exact (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSec M _ _ (IsIso.inv_hom_id (pullback.fst B.hom j)))
    ⟨_, idIso_isGen (pull_isLB hM _)⟩).symm

theorem kTriv_of_localHom (R₁ R : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsLocalRing R]
    (π : R₁ →+* R) [IsLocalHom π] (B : Over (Sp R₁)) [GrpObj B] (hB : IsAbelianScheme B) (M : LB B.left) (hM : M.IsLB)
    (hA : RelAmple B M) (Y₀ : Over (Sp R)) [GrpObj Y₀] (b : Y₀.left ⟶ B.left) (hb : IsGrpPullback Y₀ B (spMap π) b)
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hK : KTriv Y₀ N₀) : KTriv B M := by
  obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hM hN₀ hB hA hb hiso hK (IsLocalRing.closedPoint R)
  have hcl : (spMap π) (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint R₁ := by
    exact IsLocalRing.comap_closedPoint π
  have htop : U = ⊤ := by
    rw [hcl] at hU
    exact top_le_iff.1 fun p _ => (IsLocalRing.specializes_closedPoint p).mem_open U.2 hU
  subst htop
  have hL := pull_isLB hM (pullback.fst B.hom (⊤ : (Sp R₁).Opens).ι)
  have hPB := isGrpPullback_pullback B (⊤ : (Sp R₁).Opens).ι
  have hAb : IsAbelianScheme ((Over.pullback (⊤ : (Sp R₁).Opens).ι).obj B) := by
    have := hB.comm
    refine ⟨?_, MorphismProperty.of_isPullback (P := @Smooth) hPB.1 hB.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hPB.1 hB.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hPB.1 hB.geomConnected⟩
    rw [isCommMonObj_iff_isMulCommutative]
    intro T
    refine ⟨⟨fun x y => Over.OverMorphism.ext (hPB.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hPB.2 T x y (pushPt hPB.1.w x) (pushPt hPB.1.w y) rfl rfl,
      ← hPB.2 T y x (pushPt hPB.1.w y) (pushPt hPB.1.w x) rfl rfl, _root_.mul_comm]
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ PUnit (fun _ => ⊤) B _ _ (by simp)
    (fun _ => isGrpPullback_pullback B _) _ _ hM (fun _ => hL) (fun _ => GlobalTheory.lbIso_refl hL) hB
    (fun _ => hAb) (fun _ => H)

end GlobalTheory.SharpLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPrincipalArtinianOfPrincipalPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.PrincipalIntegral
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArtinPrinc

theorem surj_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀}
    (hP : IsPullback f₁ f₂ g₁ g₂) (hs : Function.Surjective g₂) : Function.Surjective f₁ := by
  have h := hP.map (forget CommRingCat)
  intro r
  obtain ⟨r₂, hr₂⟩ := hs (g₁ r)
  obtain ⟨x, hx, -⟩ := ((Types.isPullback_iff _ _ _ _).1 h).2.2 r r₂ hr₂.symm
  exact ⟨x, hx⟩

theorem principal_of_pull : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := by
  intro g n _ _ P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart _ hs₂ _ β c c₁ hpb hc₁
  obtain ⟨φ, φ₂, hφ, hsq, hw, -⟩ := hpb
  obtain ⟨hA₁, hK₁⟩ := hc₁
  have hl : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hf₁ : Function.Surjective f₁.hom := surj_of_isPullback hP hs₂
  let f := Spec.map f₁
  have hPc : cls c₁.P c₁.isLB = pull φ₂ (cls c.P c.isLB) := (cls_eq_iff _ (pull_isLB c.isLB _)).2 hw
  have hpair : ∀ {T : Over (Spec P)} {T' : Over (Spec R₁)} (u : T'.left ⟶ T.left) (a b : T ⟶ c.A)
      (a' b' : T' ⟶ c₁.A), a'.left ≫ φ = u ≫ a.left → b'.left ≫ φ = u ≫ b.left →
      GlobalTheory.PrincipalIntegral.pair (cls c₁.P c₁.isLB) a' b' = pull u (GlobalTheory.PrincipalIntegral.pair (cls c.P c.isLB) a b) := fun u a b a' b' ha hb => by
    rw [GlobalTheory.PrincipalIntegral.pair, GlobalTheory.PrincipalIntegral.pair, hPc, ← pull_comp, ← pull_comp, SiegelDescent.lift_comp_square hsq u a b a' b' ha hb]
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hD₁ : c₁.diag.IsLB := pull_isLB c₁.isLB _
  have hd : cls c₁.diag hD₁ = pull φ (cls c.diag hD) :=
    hpair φ (𝟙 c.A) (𝟙 c.A) (𝟙 c₁.A) (𝟙 c₁.A) (by simp) (by simp)
  have hdiso : LBIso c₁.diag (c.diag.pull φ) := by
    refine (cls_eq_iff hD₁ (pull_isLB hD _)).1 ?_
    rw [cls_pull hD, hd]
  haveI := c.ab.proper
  haveI := c.ab.smooth
  have hA : Out.RelAmple c.A c.diag :=
    GlobalTheory.SharpLift.relAmple_of_closed_proper P c.A c.diag hD R₁ f₁.hom hf₁ c₁.A φ hφ.1 c₁.diag hD₁ hdiso hA₁
  refine ⟨hA, fun T x hx => ?_⟩
  obtain ⟨hpos, hdet⟩ := isE8_W8
  let G := Out.powObj c.A 8
  let pr : Fin 8 → (G ⟶ c.A) := Out.powPr c.A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over (Spec P)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hG : IsAbelianScheme G := AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 7
  let G' := (Over.pullback f).obj G
  let ψ : G'.left ⟶ G.left := Pdiv.PullbackComparison.pφ f G
  have hψ : IsGrpPullback G' G f ψ := Pdiv.PullbackComparison.isGrpPullback f G
  choose pr' hpr using fun u => SharpPull.exists_lift hψ hφ (pr u)
  have hmon' : ∀ u, IsMonHom (pr' u) := fun u => SharpPull.isMonHom_lift hψ hφ (hpr u)
  have huniv' : ∀ (T : Over (Spec R₁)) (y : Fin 8 → (T ⟶ c₁.A)), ∃! x : T ⟶ G', ∀ u, x ≫ pr' u = y u :=
    fun T y => by
    obtain ⟨x₀, hx₀, hu⟩ := huniv (Over.mk (T.hom ≫ f)) (fun u => pushHom hφ T (y u))
    obtain ⟨x, rfl⟩ := SharpPull.push_surj hψ x₀
    refine ⟨x, fun u => SharpPull.push_inj hφ ?_, fun x' hx' => SharpPull.push_inj hψ (hu _ fun u => ?_)⟩
    · rw [SharpPull.push_comp hψ hφ (hpr u), hx₀ u]
    · rw [← SharpPull.push_comp hψ hφ (hpr u), hx' u]
  let L := LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) fun uv => W8 uv.1 uv.2
  let L' := LB.LinComb c₁.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr' uv.1) (pr' uv.2)).left)
    fun uv => W8 uv.1 uv.2
  have hL : L.IsLB := LB.isLB_linComb c.isLB _ _
  have hL' : L'.IsLB := LB.isLB_linComb c₁.isLB _ _
  have hLW : cls L hL = quad (cls c.P c.isLB) W8 pr := cls_linComb c.isLB _ _ _
  have hLW' : cls L' hL' = quad (cls c₁.P c₁.isLB) W8 pr' := cls_linComb c₁.isLB _ _ _
  have hiso : LBIso L' (L.pull ψ) := by
    refine (cls_eq_iff hL' (pull_isLB hL _)).1 ?_

    rw [cls_pull hL, hLW, hLW', quad, quad, map_sum]
    exact Finset.sum_congr rfl fun uv _ => by rw [map_zsmul, hpair ψ _ _ _ _ (hpr uv.1) (hpr uv.2)]
  have hadd := pair_mul c hl.globalFns hA
  have hadd' := pair_mul c₁ hl.globalFns hA₁
  have hK' : Out.KTriv G' L' := kTriv_of_kernel hadd' (pair_comm c₁) hmon' huniv' hL' hLW' hdet fun T x hx =>
    hK₁ T x ((cls_eq_zero_iff (pull_isLB c₁.isLB _)).1 hx)
  have hAL : Out.RelAmple G L :=
    PosDefAmple.relAmple_linComb_of_posDef hl.globalFns g n 8 _ _ _ _ c G pr W8 hmon huniv hA hpos
  haveI : IsLocalRing R₁ := IsLocalRing.of_surjective' f₁.hom hf₁
  haveI : IsLocalHom f₁.hom := Function.Surjective.isLocalHom f₁.hom hf₁
  have hK : Out.KTriv G L := GlobalTheory.SharpLift.kTriv_of_localHom P R₁ f₁.hom G hG L hL hAL G' ψ hψ L' hL' hiso hK'
  have hx' : GlobalTheory.PrincipalIntegral.pair (cls c.P c.isLB) (snd c.A T ≫ x) (fst c.A T) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 hx
  exact kernel_of_kTriv (n := 8) (G := G) hadd (pair_comm c) hmon huniv hL hLW (0 : Fin 8) hK T x hx'

end GlobalTheory.ArtinPrinc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPrincipalArtinianOfPrincipalPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegel_principal_artinian_of_principal_pullback : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := by
  first | exact @GlobalTheory.ArtinPrinc.principal_of_pull | exact GlobalTheory.ArtinPrinc.principal_of_pull | (intros; apply GlobalTheory.ArtinPrinc.principal_of_pull <;> assumption)
end
end
