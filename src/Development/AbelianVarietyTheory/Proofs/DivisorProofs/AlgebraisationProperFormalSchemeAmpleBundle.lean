module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CancelPowersOfCechLineBundlesStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphismsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveAlgebraisationFormalEmbeddingComStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleCompatibleSectionsThickeningTower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoAlgebraisedPowersCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleIsoLocalUnitsCompOfPullbackSections

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem gs_comp_stalkMap {Z Y X : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) (U : X.Opens) (h : F (r z) ∈ U)
    (a : Γ(X, U)) :
    gs (r ≫ F) z U a = (Scheme.Hom.stalkMap r z).hom (gs F (r z) U a) := by
  rw [← gs_pull r F z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) F (r z) U h, Category.id_comp]

theorem gm_val_stalkMap {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : r z ∈ V) (u : Γ(Y, V)ˣ) :
    ((gm r z V u : (Z.presheaf.stalk z)ˣ) : Z.presheaf.stalk z) =
      (Scheme.Hom.stalkMap r z).hom ((gm (𝟙 Y) (r z) V u : (Y.presheaf.stalk (r z))ˣ) : Y.presheaf.stalk (r z)) := by
  rw [← gs_unit r z V h, ← gs_unit (𝟙 Y) (r z) V h, gs_stalkMap r z V h]

theorem gw_comp_of_rel : ∀ (X Y' Y : Scheme.{0}) (b' : Y' ⟶ X) (β : Y ⟶ Y') (b : Y ⟶ X), β ≫ b' = b → ∀ (A : LB X) (H' : LB Y') (H : LB Y) (w' : LB.Iso H' (A.pull b')) (v : LB.Iso H (H'.pull β)) (w : LB.Iso H (A.pull b)) (ι : Type) (s : ι → LB.Sec A) (s' : ι → LB.Sec H') (s'' : ι → LB.Sec H), (∀ j, Rel b' w' (s j) (s' j)) → (∀ j, Rel β v (s' j) (s'' j)) → (∀ j, Rel b w (s j) (s'' j)) → (⨆ j, nonzeroLocus (s'' j) = ⊤) → ∀ z k k' k'', b z ∈ A.U k → β z ∈ H'.U k' → z ∈ H.U k'' → Geo.Tor.gw w (𝟙 _) z k k'' = Geo.Tor.gw w' β z k k' * Geo.Tor.gw v (𝟙 _) z k' k'' := by
  intro X Y' Y b' β b hb A H' H w' v w ι s s' s'' h₁ h₂ h₃ hc z k k' k'' hk hk' hk''
  subst hb

  have hz : z ∈ ⨆ j, nonzeroLocus (s'' j) := by rw [hc]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  obtain ⟨k₀, hk₀, hu₀⟩ := (mem_nonzeroLocus (s'' j) z).1 hj
  have hu : IsUnit (gs (𝟙 Y) z (H.U k'') ((s'' j).f k'')) := by
    rw [gs_compat (s'' j) (𝟙 Y) z hk'' hk₀]
    exact (Units.isUnit _).mul hu₀
  have hkb : b' (β z) ∈ A.U k := hk
  have e₁ := h₁ j (β z) k k' hkb hk'
  have e₂ := h₂ j z k' k'' hk' hk''
  have e₃ := h₃ j z k k'' hk hk''
  have hV : β z ∈ (A.pull b').U (fun _ => k) ⊓ H'.U k' := ⟨mem_pull.2 hkb, hk'⟩
  have e₁' := congrArg (Scheme.Hom.stalkMap β z).hom e₁
  rw [map_mul, ← gs_comp_stalkMap β b' z _ hkb, ← gs_stalkMap β z _ hk'] at e₁'
  have hw' : ((Geo.Tor.gw w' β z k k' : (Y.presheaf.stalk z)ˣ) : Y.presheaf.stalk z) =
      (Scheme.Hom.stalkMap β z).hom ((Geo.Tor.gw w' (𝟙 _) (β z) k k' : (Y'.presheaf.stalk (β z))ˣ) :
        Y'.presheaf.stalk (β z)) :=
    gm_val_stalkMap β z _ hV _
  rw [← hw', e₂] at e₁'
  rw [e₃, ← _root_.mul_assoc, ← Units.val_mul] at e₁'
  exact Units.ext (hu.mul_left_inj.1 e₁')

end GlobalTheory.FormalAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleIsoLocalUnitsCompOfPullbackSectionsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections : ∀ (X Y' Y : Scheme.{0}) (b' : Y' ⟶ X) (β : Y ⟶ Y') (b : Y ⟶ X), β ≫ b' = b → ∀ (A : LB X) (H' : LB Y') (H : LB Y) (w' : LB.Iso H' (A.pull b')) (v : LB.Iso H (H'.pull β)) (w : LB.Iso H (A.pull b)) (ι : Type) (s : ι → LB.Sec A) (s' : ι → LB.Sec H') (s'' : ι → LB.Sec H), (∀ j, Rel b' w' (s j) (s' j)) → (∀ j, Rel β v (s' j) (s'' j)) → (∀ j, Rel b w (s j) (s'' j)) → (⨆ j, nonzeroLocus (s'' j) = ⊤) → ∀ z k k' k'', b z ∈ A.U k → β z ∈ H'.U k' → z ∈ H.U k'' → Geo.Tor.gw w (𝟙 _) z k k'' = Geo.Tor.gw w' β z k k' * Geo.Tor.gw v (𝟙 _) z k' k'' := by
  first | exact @GlobalTheory.FormalAlg.gw_comp_of_rel | exact GlobalTheory.FormalAlg.gw_comp_of_rel | (intros; apply GlobalTheory.FormalAlg.gw_comp_of_rel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoZpowLocalUnitsPow

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

open ReciprocityTheory.ChartRestriction.G.Semi

theorem commGroup_mul_inv_zpow {G : Type} [CommGroup G] (x y : G) (a : ℤ) : (x * y⁻¹) ^ a = x ^ a * (y ^ a)⁻¹ := by
  rw [mul_zpow, inv_zpow]

theorem div_pull_pw_g {X Y : Scheme.{0}} (A : LB X) (H : LB Y) (φ : Y ⟶ X) (a : ℤ) (p q : (PUnit → A.ι) × H.ι) :
    (LB.div ((GlobalTheory.AbLaw.pw A a).pull φ) (GlobalTheory.AbLaw.pw H a)).g p q =
      (((LB.div (A.pull φ) H).g p q) ^ a : Γ(Y, (LB.div (A.pull φ) H).U p ⊓ (LB.div (A.pull φ) H).U q)ˣ) := by
  show res _ (∏ _k : PUnit, res _ (pullU φ _ (A.g _ _ ^ a)) ^ (1 : ℤ)) * (res _ (H.g p.2 q.2 ^ a))⁻¹ =
    (res _ (∏ _k : PUnit, res _ (pullU φ _ (A.g _ _)) ^ (1 : ℤ)) * (res _ (H.g p.2 q.2))⁻¹) ^ a
  simp only [Fintype.prod_unique, zpow_one, map_zpow]
  exact (commGroup_mul_inv_zpow _ _ a).symm

theorem lbIso_pw_pull_gw : ∀ (X Y : Scheme.{0}) (φ : Y ⟶ X) (A : LB X) (H : LB Y) (w : LB.Iso H (A.pull φ)), w.IsGen → ∀ a : ℤ, ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw H a) ((GlobalTheory.AbLaw.pw A a).pull φ), wa.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : H.ι), φ (r z) ∈ A.U k → r z ∈ H.U k' → Geo.Tor.gw wa r z k k' = Geo.Tor.gw w r z k k' ^ a := by
  intro X Y φ A H w hw a
  refine ⟨⟨fun p => w.s p ^ a⟩, ?_, ?_⟩
  · intro p q
    have e := congrArg (· ^ a) (hw p q)
    simp only [mul_zpow, ← map_zpow] at e
    exact e.trans (congrArg (· * res _ (w.s q ^ a)) (div_pull_pw_g A H φ a p q).symm)
  · intro Z r z k k' _ _
    exact map_zpow _ _ a

end GlobalTheory.FormalAlg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoZpowLocalUnitsPowStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_bundleIso_zpow_local_units_pow : ∀ (X Y : Scheme.{0}) (φ : Y ⟶ X) (A : LB X) (H : LB Y) (w : LB.Iso H (A.pull φ)), w.IsGen → ∀ a : ℤ, ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw H a) ((GlobalTheory.AbLaw.pw A a).pull φ), wa.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : H.ι), φ (r z) ∈ A.U k → r z ∈ H.U k' → Geo.Tor.gw wa r z k k' = Geo.Tor.gw w r z k k' ^ a := by
  first | exact @GlobalTheory.FormalAlg.lbIso_pw_pull_gw | exact GlobalTheory.FormalAlg.lbIso_pw_pull_gw | (intros; apply GlobalTheory.FormalAlg.lbIso_pw_pull_gw <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleAlgebraisationGeneratedSystem

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

theorem exists_lb_of_generated_system_proper : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → (∀ e, ⨆ i, nonzeroLocus (s e i) = ⊤) → ∃ (M : LB X.left) (s' : Fin (n + 1) → LB.Sec M) (w : ∀ e, LB.Iso (H e) (M.pull (b e))), M.IsLB ∧ ∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j) := by
  intro R _ _ I hcI X hX Y β b hb hbb H v hH n s hs hgen
  obtain ⟨P, f, O, t, hO, hva, hP⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal R n ⊥ (fun F hF d => by
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  choose c w hc' hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy R P f O n t hO hva _
    ((Y e).hom ≫ thick R I e) (H e) (s e) (hH e).1 (hgen e) (fun d F hF h k => by
      obtain ⟨m, hm⟩ := (hP d F hF).1 h 0
      have : F = 0 := by
        rw [Ideal.mem_bot] at hm
        exact ((MvPolynomial.isRegular_X (n := (0 : Fin (n + 1)))).pow m).left (by simpa using hm)
      rw [this, map_zero])
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := fun e => by
    rw [← (hb (e + 1)).w, ← Category.assoc, hbb, (hb e).w]
  have hcc : ∀ e, β e ≫ c (e + 1) = c e := fun e => by
    have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hO (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections R P f O n t hO hva _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hc', hc', c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
  haveI hPp : IsProper f := GlobalTheory.AbLaw.isProper_of_isProjBy R P f ⟨O, hO, n, t, hva⟩
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.formalAlgebraisation_morphisms' R I hcI X (Over.mk f) hX (inferInstanceAs (IsSeparated f))
    (inferInstanceAs (LocallyOfFiniteType f)) (inferInstanceAs (QuasiCompact f)) Y β b hb hbb
    c hc' hcc
  have hM : (O.pull g.left).IsLB := LB.isLB_pull hO _
  obtain ⟨s', hs'⟩ := GlobalTheory.MorAlg.exists_isPull g.left hO t
  have key : ∀ e, GlobalTheory.MorAlg.IsPull (b e) s' (s e) := fun e =>
    GlobalTheory.MorAlg.IsPull.cancel hO hM (hH e).1 hs' (by rw [hg e]; exact ⟨w e, hw e, hr e⟩)
  choose w' hw' cw using key
  exact ⟨O.pull g.left, s', w', hM, fun e => ⟨hw' e, fun j => cw e j⟩⟩

end GlobalTheory.FormalAlg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleAlgebraisationGeneratedSystemStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_lineBundle_algebraisation_generatedSystem : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → (∀ e, ⨆ i, nonzeroLocus (s e i) = ⊤) → ∃ (M : LB X.left) (s' : Fin (n + 1) → LB.Sec M) (w : ∀ e, LB.Iso (H e) (M.pull (b e))), M.IsLB ∧ ∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j) := by
  first | exact @GlobalTheory.FormalAlg.exists_lb_of_generated_system_proper | exact GlobalTheory.FormalAlg.exists_lb_of_generated_system_proper | (intros; apply GlobalTheory.FormalAlg.exists_lb_of_generated_system_proper <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleCompatibleSectionsThickeningTowerStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_veryAmple_compatible_sections_thickeningTower : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → RelAmple (Y 0) (N 0) → ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ, c = a ∨ c = a + 1 → ∀ v : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)), (∀ e, (v e).IsGen) → ∃ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N e) c)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) ∧ ∀ e, VeryAmpleBy (Y e).hom (GlobalTheory.AbLaw.pw (N e) c) (s e) := by
  first | exact @GlobalTheory.FormalAlg.TowerVA.exists_veryAmple_compatible | exact GlobalTheory.FormalAlg.TowerVA.exists_veryAmple_compatible | (intros; apply GlobalTheory.FormalAlg.TowerVA.exists_veryAmple_compatible <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationProperFormalSchemeAmpleBundle

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem isClosedImmersion_lift_id {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : 𝟙 X ≫ f = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id R))) :
    IsClosedImmersion (pullback.lift (𝟙 X) f h) := by
  have hi : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 _ from rfl, Spec.map_id]
    infer_instance
  have e : pullback.lift (𝟙 X) f h = inv (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id R)))) :=
    IsIso.eq_inv_of_inv_hom_id (pullback.lift_fst _ _ _)
  rw [e]
  infer_instance

theorem veryAmpleBy_of_lbIso {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {H H'' : LB X} (hH : H.IsLB) (hH'' : H''.IsLB) (hI : LBIso H H'') {n : ℕ} {s : Fin (n + 1) → LB.Sec H}
    (hs : VeryAmpleBy f H s) : ∃ s'' : Fin (n + 1) → LB.Sec H'', VeryAmpleBy f H'' s'' := by
  obtain ⟨w, hw⟩ := LBIso.trans hH'' hH (pull_isLB hH _) (LBIso.symm hI) (LBIso.symm (GlobalTheory.lbIso_pull_id hH))
  choose s'' hs'' using fun j => (GlobalTheory.SecPullIso.section_pull X X (𝟙 X) H H'' w hH hH'' hw (s j)).1.exists
  exact ⟨s'', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R (RingHom.id R) X f (𝟙 X)
    (by rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 _ from rfl, Spec.map_id]; simp)
    (isClosedImmersion_lift_id f _) H'' w s'' hH'' hw fun j => hs'' j⟩

end GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem formalAlgebraisation_schemes : GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  intro R _ _ I hI Y β hβ hY N hN hNN hA
  choose v hv using hNN
  obtain ⟨a, ha1, hlift⟩ := GlobalTheory.T.exists_veryAmple_compatible_sections_thickeningTower R I Y β hβ N hN hA
  have hpw : ∀ (c : ℤ) (e : ℕ), ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)),
      wa.IsGen ∧ ∀ (z : (Y e).left) (k : (N (e + 1)).ι) (k' : (N e).ι), β e z ∈ (N (e + 1)).U k → z ∈ (N e).U k' →
        Geo.Tor.gw wa (𝟙 _) z k k' = Geo.Tor.gw (v e) (𝟙 _) z k k' ^ c := fun c e => by
    obtain ⟨wa, h1, h2⟩ := GlobalTheory.T.exists_bundleIso_zpow_local_units_pow (Y (e + 1)).left (Y e).left (β e) (N (e + 1)) (N e) (v e) (hv e) c
    exact ⟨wa, h1, fun z k k' hk hk' => h2 (Y e).left (𝟙 _) z k k' hk hk'⟩
  choose va hva hvaw using hpw (a : ℤ)
  choose vb hvb hvbw using hpw ((a + 1 : ℕ) : ℤ)
  obtain ⟨n, s, hsRel, hsVA⟩ := hlift a (Or.inl rfl) va hva
  obtain ⟨n₂, s₂, hs₂Rel, hs₂VA⟩ := hlift (a + 1) (Or.inr rfl) vb hvb
  obtain ⟨B, H', s', b, w, hH', hVA', hpb, hcomp, hw, -⟩ := GlobalTheory.T.exists_projective_algebraisation_formalEmbedding_complete R I hI Y β hβ
    (fun e => GlobalTheory.AbLaw.pw (N e) a) va (fun e => ⟨isLB_pw (hN e) _, hva e⟩) n s hsRel (hsVA 0)
  have hBp : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy R B.left B.hom ⟨H', hH', n, s', hVA'⟩
  obtain ⟨M₂, s₂', w', hM₂, hw'⟩ := GlobalTheory.T.exists_lineBundle_algebraisation_generatedSystem R I hI B hBp Y β b hpb hcomp
    (fun e => GlobalTheory.AbLaw.pw (N e) ((a + 1 : ℕ) : ℤ)) vb (fun e => ⟨isLB_pw (hN e) _, hvb e⟩) n₂ s₂ hs₂Rel
    (fun e => (hs₂VA e).1)
  have c1 : ∀ e z k l' l, b e z ∈ H'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
      Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ (a : ℤ) := by
    intro e z k l' l h1 h2 h3
    rw [← hvaw e z l' l h2 h3]
    exact GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections B.left (Y (e + 1)).left (Y e).left (b (e + 1)) (β e) (b e) (hcomp e) H'
      (GlobalTheory.AbLaw.pw (N (e + 1)) a) (GlobalTheory.AbLaw.pw (N e) a) (w (e + 1)) (va e) (w e) (Fin (n + 1)) s' (s (e + 1)) (s e)
      (fun j => (hw (e + 1)).2 j) (fun j => hsRel e j) (fun j => (hw e).2 j) (hsVA e).1 z k l' l h1 h2 h3
  have c2 : ∀ e z k l' l, b e z ∈ M₂.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
      Geo.Tor.gw (w' e) (𝟙 _) z k l =
        Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ ((a + 1 : ℕ) : ℤ) := by
    intro e z k l' l h1 h2 h3
    rw [← hvbw e z l' l h2 h3]
    exact GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections B.left (Y (e + 1)).left (Y e).left (b (e + 1)) (β e) (b e) (hcomp e) M₂
      (GlobalTheory.AbLaw.pw (N (e + 1)) ((a + 1 : ℕ) : ℤ)) (GlobalTheory.AbLaw.pw (N e) ((a + 1 : ℕ) : ℤ)) (w' (e + 1)) (vb e) (w' e)
      (Fin (n₂ + 1)) s₂' (s₂ (e + 1)) (s₂ e)
      (fun j => (hw' (e + 1)).2 j) (fun j => hs₂Rel e j) (fun j => (hw' e).2 j) (hs₂VA e).1 z k l' l h1 h2 h3
  have hiso := GlobalTheory.T.lineBundleIso_algebraised_powers_compatible R I hI B hBp Y β b hpb hcomp N v hN (a : ℤ) ((a + 1 : ℕ) : ℤ) H' M₂ hH' hM₂ w w'
    (fun e => ⟨(hw e).1, (hw' e).1⟩) c1 c2
  have hcast : ((a + 1 : ℕ) : ℤ) = (a : ℤ) + 1 := by push_cast; rfl
  rw [hcast] at hiso
  have hM : (GlobalTheory.AbLaw.tw M₂ H' (-1)).IsLB := isLB_tw hM₂ hH' _
  have hH'M : LBIso H' (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M₂ H' (-1)) a) := GlobalTheory.T.cancel_powers_of_cech_line_bundles.2 B.left H' M₂ a hH' hM₂ hiso
  have hNM : ∀ e, LBIso (N e) ((GlobalTheory.AbLaw.tw M₂ H' (-1)).pull (b e)) := fun e =>
    GlobalTheory.T.cancel_powers_of_cech_line_bundles.1 B.left (Y e).left (b e) H' M₂ (N e) a hH' hM₂ (hN e) ⟨w e, (hw e).1⟩
      (hcast ▸ ⟨w' e, (hw' e).1⟩)
  obtain ⟨s'', hs''⟩ := veryAmpleBy_of_lbIso B.hom hH' (isLB_pw hM _) hH'M hVA'
  exact ⟨B, GlobalTheory.AbLaw.tw M₂ H' (-1), b, hBp, hM,
    (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B _ hM).2 ⟨a, ha1, n, s'', hs''⟩, hpb, hcomp, hNM⟩

end GlobalTheory.FormalAlg
end
end
end
