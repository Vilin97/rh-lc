module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoVal

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A] [IsCommMonObj A'] {L : RigLB A}
  {L' : RigLB A'} (c : CubicalStr A L) (c' : CubicalStr A' L') {f : S' ⟶ S} {Φ : A'.left ⟶ A.left} (hG : GlobalFnsSt)
  (hA : IsAbelianScheme A') (gp : IsGrpPullback A' A f Φ) (w : LB.Iso L'.L (L.L.pull Φ)) (hwg : w.IsGen)
include hG hA hwg

theorem cub_w₀ {T' : Over S'} {z : T'.left} {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J') (x x' y : T' ⟶ A') :
    val (L := L.L) (φ := thφ A (x3 A)) (ε := thε) c.t ((lift x (lift x' y)).left ≫ (cubeMapOf gp).F3) z J =
      (∏ I : thK.{0}, gw w ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) z
        (J (((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) ≫ (cubeMapOf gp).F))
        (J' ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I)) ^ thε I) * cubV c' z J' x x' y := by
  have hPG : PGen w := (isGen_iff w).1 hwg
  obtain ⟨t, ht, htv⟩ := exists_up hPG L.isLB L'.isLB (φ' := thφ A' (x3 A')) (ε := thε) c'.t c'.isGen
  have hpt : ∀ I : thK.{0}, thφ A' (x3 A') I ≫ Φ = (cubeMapOf gp).F3 ≫ thφ A (x3 A) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  have hFF : FormEq (fun I => thφ A' (x3 A') I ≫ Φ) thε
      (fun I => (cubeMapOf gp).F3 ≫ thφ A (x3 A) I) thε := by
    unfold FormEq
    intro U _ h
    simp only [hpt]
  have hu := pullGen_isGen L.L (thφ A (x3 A)) thε c.t c.isGen (cubeMapOf gp).F3
  have he : (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left ≫ (snd A' (A' ⊗ A')).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, lift_fst_snd, Over.id_left]
  have hp := surj_snd hG hA (A' ⊗ A')
  have hE : (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left ≫ (cubeMapOf gp).F3 =
      (lift (1 : Over.mk ((A' ⊗ A').hom ≫ f) ⟶ A)
        (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).left := by
    apply hom_ext_triple
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3, cubeMapOf, pushPt] <;>
      exact congrArg (fun q => q.left) (map_one (pushHom gp (A' ⊗ A')))
  have hvt : ∀ (Z0 : Scheme.{0}) (r : Z0 ⟶ (G3 A').left) (z0 : Z0) (J0 : (Z0 ⟶ A.left) → L.L.ι)
      (J0' : (Z0 ⟶ A'.left) → L'.L.ι), Good L.L z0 J0 → Good L'.L z0 J0' →
      val t r z0 J0 = (∏ I : thK.{0}, gw w (r ≫ thφ A' (x3 A') I) z0 (J0 ((r ≫ thφ A' (x3 A') I) ≫ Φ))
        (J0' (r ≫ thφ A' (x3 A') I)) ^ thε I) *
        val (L := L'.L) (φ := thφ A' (x3 A')) (ε := thε) c'.t r z0 J0' := by
    intro Z0 r z0 J0 J0' hJ0 hJ0'
    have hm1 : r z0 ∈ LB.wchart L.L (fun I => thφ A' (x3 A') I ≫ Φ)
        (fun I => J0 (r ≫ (thφ A' (x3 A') I ≫ Φ))) :=
      Set.mem_iInter.2 fun I => hJ0 (r ≫ (thφ A' (x3 A') I ≫ Φ))
    have hm2 : r z0 ∈ LB.wchart L'.L (thφ A' (x3 A')) (fun I => J0' (r ≫ thφ A' (x3 A') I)) :=
      Set.mem_iInter.2 fun I => hJ0' (r ≫ thφ A' (x3 A') I)
    refine (htv Z0 r z0 _ _ hm1 hm2).trans ?_
    simp only [pw, val, Category.assoc] <;> rfl
  have hcov : ∀ q : A'.left, ∃ i, q ∈ L'.L.U i := fun q => by
    have hq : q ∈ (⨆ i, L'.L.U i) := by
      rw [L'.isLB.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hq
  have ac : ∀ {U : Type} [CommGroup U] (a b c d : U), a * b⁻¹ * c⁻¹ * a⁻¹ * d * b * c * d⁻¹ = 1 := by
    intro U _ a b c d
    have e1 : a * b⁻¹ * c⁻¹ * a⁻¹ * d * b * c * d⁻¹ = (a * a⁻¹) * (b⁻¹ * b) * (c⁻¹ * c) * (d * d⁻¹) := by
      ac_rfl
    rw [e1]
    simp
  have key := gen_unique' L.isLB hFF (snd A' (A' ⊗ A')).left
    (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left he hp hu ht
    (fun q Jq hJq => by
      obtain ⟨J'q, hJ'q⟩ : ∃ J'q : ((A' ⊗ A').left ⟶ A'.left) → L'.L.ι, Good L'.L q J'q :=
        ⟨fun ψ => Classical.choose (hcov (ψ q)), fun ψ => Classical.choose_spec (hcov (ψ q))⟩
      obtain ⟨hh, hhd⟩ : ∃ hh : ((A' ⊗ A').left ⟶ A'.left) → ((A' ⊗ A').left.presheaf.stalk q)ˣ,
          ∀ ψ, hh ψ = gw w ψ q (Jq (ψ ≫ Φ)) (J'q ψ) := ⟨_, fun _ => rfl⟩
      have f1 : cubV c (T := Over.mk ((A' ⊗ A').hom ≫ f)) q Jq 1
          (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')) = 1 := by
        have e := val_corr hJq (c.face 0) (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))).left
        rw [val_one] at e
        refine (Eq.trans ?_ (val_cub c (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))) hJq (pzero A _) (x2 A 0) (x2 A 1)).symm).trans e
        congr 1 <;> simp [x2, pzero, Hom.one_def]
      have f2 : val (L := L'.L) (φ := thφ A' (x3 A')) (ε := thε) c'.t
          (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left q J'q = 1 := by
        have e := val_corr hJ'q (c'.face 0) (lift (fst A' A') (snd A' A')).left
        rw [val_one] at e
        refine (Eq.trans ?_ (val_cub c' (lift (fst A' A') (snd A' A')) hJ'q (pzero A' _) (x2 A' 0) (x2 A' 1)).symm).trans e
        congr 1 <;> simp [x2, pzero, Hom.one_def]
      have f3 := prod_cub (T := A' ⊗ A') (1 : A' ⊗ A' ⟶ A') (fst A' A') (snd A' A') hh
      erw [val_pull]
      rw [hE]
      refine f1.trans ?_
      refine Eq.trans ?_ (hvt _ _ q Jq J'q hJq hJ'q).symm
      rw [f2, _root_.mul_one]
      simp only [← hhd]
      rw [f3]
      simp only [_root_.one_mul]
      exact (ac _ _ _ _).symm
      all_goals exact hJq)
    T'.left (lift x (lift x' y)).left z J hJ
  erw [val_pull] at key
  refine key.trans ((hvt _ _ z J J' hJ hJ').trans ?_)
  rfl
  all_goals exact hJ


omit hG hA hwg [GrpObj A] [GrpObj A'] [IsCommMonObj A] [IsCommMonObj A'] in
def Om {M : LB A.left} {M' : LB A'.left} (w : LB.Iso M' (M.pull Φ)) {Z : Scheme.{0}} {s' : Z ⟶ S'} (z : Z)
    (J : (Z ⟶ A.left) → M.ι) (J' : (Z ⟶ A'.left) → M'.ι) (x : Over.mk s' ⟶ A') : (Z.presheaf.stalk z)ˣ :=
  gw w (show Z ⟶ _ from x.left) z (J (x.left ≫ Φ)) (J' x.left)


omit hG hA hwg in
def cubZ {Z : Scheme.{0}} {s : Z ⟶ S} (z : Z) (J : (Z ⟶ A.left) → L.L.ι) (a b d : Over.mk s ⟶ A) : (Z.presheaf.stalk z)ˣ :=
  cubV c (T := Over.mk s) z J a b d


include gp in
theorem cub_w {Z : Scheme.{0}} {s' : Z ⟶ S'} {s : Z ⟶ S} {z : Z} {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J')
    (a b d : Over.mk s' ⟶ A') (a₀ b₀ d₀ : Over.mk s ⟶ A) (ha : a.left ≫ Φ = a₀.left) (hb : b.left ≫ Φ = b₀.left)
    (hd : d.left ≫ Φ = d₀.left) : cubZ c z J a₀ b₀ d₀ =
      Om w z J J' (a * b * d) * (Om w z J J' (a * b))⁻¹ * (Om w z J J' (a * d))⁻¹ * (Om w z J J' (b * d))⁻¹ * Om w z J J' a *
        Om w z J J' b * Om w z J J' d * (Om w z J J' (1 : Over.mk s' ⟶ A'))⁻¹ * cubZ c' z J' a b d := by
  have hF3 : (lift a (lift b d)).left ≫ (cubeMapOf gp).F3 = (lift a₀ (lift b₀ d₀)).left := by
    apply hom_ext_triple
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3, cubeMapOf]
    · exact ha
    · exact hb
    · exact hd
  have h0 := cub_w₀ (c := c) (c' := c') (hG := hG) (hA := hA) (gp := gp) (w := w) (hwg := hwg)
    (hJ := hJ) (hJ' := hJ') (x := a) (x' := b) (y := d)
  rw [hF3] at h0
  refine h0.trans ?_
  congr 1
  exact prod_cub a b d (fun ψ => gw w ψ z (J (ψ ≫ (cubeMapOf gp).F)) (J' ψ))

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCubicalStructureGenericFibre

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

open GlobalTheory.Poinc.Tors

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericCube

theorem exists_iso_section {X H Y : Scheme.{0}} {L : LB X} {M : LB H} {f : Y ⟶ H} {ψ : Y ⟶ X} (g : H ⟶ Y)
    (hg : g ≫ f = 𝟙 H) (w : LB.Iso (M.pull f) (L.pull ψ)) (hw : w.IsGen) :
    ∃ w' : LB.Iso M (L.pull (g ≫ ψ)), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) (j : L.ι) (k : M.ι),
      ψ (g (r z)) ∈ L.U j → r z ∈ M.U k → Geo.Tor.gw w' r z j k = Geo.Tor.gw w (r ≫ g) z j (fun _ => k) := by
  have mm : ∀ (y : H) (k : M.ι), y ∈ M.U k → g y ∈ (M.pull f).U (fun _ => k) := fun y k hy => mem_pull.2 (by
    have e : (g ≫ f) y = y := by rw [hg]; rfl
    exact (congrArg (· ∈ M.U k) e).mpr hy)
  have le : ∀ (j : L.ι) (k : M.ι), (L.pull (g ≫ ψ)).U (fun _ => j) ⊓ M.U k ≤
      g ⁻¹ᵁ ((L.pull ψ).U (fun _ => j) ⊓ (M.pull f).U (fun _ => k)) := fun j k y hy =>
    ⟨mem_pull.2 (mem_pull₂.1 hy.1), mm y k hy.2⟩
  let w' : LB.Iso M (L.pull (g ≫ ψ)) :=
    ⟨fun p => res (le (p.1 PUnit.unit) p.2) (pullU g _ (w.s (fun _ => p.1 PUnit.unit, fun _ => p.2)))⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) (j : L.ι) (k : M.ι),
      ψ (g (r z)) ∈ L.U j → r z ∈ M.U k → Geo.Tor.gw w' r z j k = Geo.Tor.gw w (r ≫ g) z j (fun _ => k) :=
    fun Z r z j k hj hk => by
      have m : r z ∈ (L.pull (g ≫ ψ)).U (fun _ => j) ⊓ M.U k := ⟨mem_pull₂.2 hj, hk⟩
      exact (gm_res r z (le j k) m _).trans (gm_pull r g z _ (le j k m) _)
  refine ⟨w', (isGen_iff w').2 fun Z r z j j' k k' hj hj' hk hk' => ?_, hv⟩
  have e := (isGen_iff w).1 hw Z (r ≫ g) z j j' (fun _ => k) (fun _ => k') hj hj' (mm _ k hk) (mm _ k' hk')
  rw [Geo.Tor.gm_pull_g M f (r ≫ g) z _ _ (mm _ k hk) (mm _ k' hk'), Category.assoc r g f, hg, Category.comp_id,
    Category.assoc] at e
  rw [hv Z r z j k hj hk, hv Z r z j' k' hj' hk']
  exact e

theorem cube_through_iso : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (h : Finset (Fin 3) → ((𝟙_ (Over (Sp V))) ⟶ G)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → h ∅ = 1 → h {0, 1} = h {0} * h {1} → h {0, 2} = h {0} * h {2} → h {1, 2} = h {1} * h {2} → h {0, 1, 2} = h {0} * h {1} * h {2} → (∀ S, IntTerm.Ext U.toUnifPre (x S) (h S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1, 2}).left) (fun _ => JA (x {0, 1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}).left) (fun _ => JA (x {0}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}).left) (fun _ => JA (x {1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}).left) (fun _ => JA (x {2}).left)) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) = cubV U.cubG z JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}) * (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1}).left) (fun _ => JA (x {0, 1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 2}).left) (fun _ => JA (x {0, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1, 2}).left) (fun _ => JA (x {1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x ∅).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h ∅).left) (fun _ => JA (x ∅).left)) := by
  intro V _ _ _ _ D A G _ _ _ U w₀ hw₀ ρ hρ c x h x0 x01 x02 x12 x012 h0 h01 h02 h12 h012 hE z JA JG hJA hJG
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback A.A G (jK V) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  obtain ⟨w, hw, hv⟩ := exists_iso_section U.gen.inv.left (congrArg (fun q => q.left) U.gen.inv_hom_id) w₀ hw₀
  have e := cub_w U.cubG c GlobalTheory.abelianSchemeLaws_all.1.globalFns A.isAb gp w hw
    (s' := jFK (R := V) (FractionRing V)) (s := jFK (R := V) (FractionRing V) ≫ jK V) (z := z) hJG hJA
    (x {0}) (x {1}) (x {2}) _ _ _ (hE {0}) (hE {1}) (hE {2})
  have k : ∀ S, Om w (s' := jFK (R := V) (FractionRing V)) z JG JA (x S) =
      Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x S).left ≫ U.gen.inv.left) z
        (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h S).left) (fun _ => JA (x S).left) := fun S => by
    refine (hv _ (x S).left z _ _ (hJG ((x S).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V))) (hJA _)).trans ?_
    exact congrArg (fun q => Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x S).left ≫ U.gen.inv.left) z
      (JG q) (fun _ => JA (x S).left)) (hE S)
  rw [← x012, ← x01, ← x02, ← x12, ← x0, k, k, k, k, k, k, k, k] at e
  refine Eq.trans ?_ (congrArg (· * _) e.symm)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, id]
  abel

end GlobalTheory.GenericCube
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCubicalStructureGenericFibreStatement

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

open GlobalTheory.Poinc.Tors

theorem _root_.GlobalTheory.T.uniformisation_cubical_structure_generic_fibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (h : Finset (Fin 3) → ((𝟙_ (Over (Sp V))) ⟶ G)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → h ∅ = 1 → h {0, 1} = h {0} * h {1} → h {0, 2} = h {0} * h {2} → h {1, 2} = h {1} * h {2} → h {0, 1, 2} = h {0} * h {1} * h {2} → (∀ S, IntTerm.Ext U.toUnifPre (x S) (h S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1, 2}).left) (fun _ => JA (x {0, 1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}).left) (fun _ => JA (x {0}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}).left) (fun _ => JA (x {1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}).left) (fun _ => JA (x {2}).left)) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) = cubV U.cubG z JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}) * (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1}).left) (fun _ => JA (x {0, 1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 2}).left) (fun _ => JA (x {0, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1, 2}).left) (fun _ => JA (x {1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x ∅).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h ∅).left) (fun _ => JA (x ∅).left)) := by
  first | exact @GlobalTheory.GenericCube.cube_through_iso | exact GlobalTheory.GenericCube.cube_through_iso | (intros; apply GlobalTheory.GenericCube.cube_through_iso <;> assumption)
end
end
