module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjByOfOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionBasesTransferTotalSpaceIso

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecBasisTransfer

def chartPullUnLinComb {X X' Y Y' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (g : Y ⟶ Y') (hc : ∀ k, g ≫ ψ' k ≫ F = ψ k) :
    ChartPull (LB.LinComb L ψ ε) (LB.LinComb (L.pull F) ψ' ε) g :=
  have pt : ∀ k (y : Y), F (ψ' k (g y)) = ψ k y := fun k y => by
    rw [← hc k]; rfl
  have le : ∀ j : K → L.ι, LB.wchart L ψ j ≤ g ⁻¹ᵁ LB.wchart (L.pull F) ψ' (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (by
      show F (ψ' k (g y)) ∈ L.U (j k)
      rw [pt k y]; exact Set.mem_iInter.1 hy k)
  { idx := fun j k _ => j k
    le := le
    g := fun y j j' hj hj' => by
      have m : g y ∈ LB.wchart (L.pull F) ψ' (fun k _ => j k) := le j hj
      have m' : g y ∈ LB.wchart (L.pull F) ψ' (fun k _ => j' k) := le j' hj'
      refine (gm_linComb L ψ ε (𝟙 Y) y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull F) ψ' ε g y _ _ m m').symm)
      refine Eq.trans ?_ (gm_pull_g L F (g ≫ ψ' k) y (fun _ => j k) (fun _ => j' k)
        (Set.mem_iInter.1 m k) (Set.mem_iInter.1 m' k)).symm
      rw [Category.assoc, hc k, Category.id_comp] }

theorem sec_eq_of_f {Y : Scheme.{0}} {N : LB Y} {s t : LB.Sec N} (e : s.f = t.f) : s = t := by
  obtain ⟨a, ha⟩ := s
  obtain ⟨b, hb⟩ := t
  cases e
  rfl

theorem pullSec_pullSec {Y Y' : Scheme.{0}} {M : LB Y} {M' : LB Y'} {g : Y ⟶ Y'} {h : Y' ⟶ Y}
    (c' : ChartPull M M' g) (c : ChartPull M' M h) (hh : g ≫ h = 𝟙 Y) (hidx : ∀ j, c.idx (c'.idx j) = j)
    (s : LB.Sec M) : GlobalTheory.SecTwist.pullSec c' (GlobalTheory.SecTwist.pullSec c s) = s := by
  refine sec_eq_of_f (funext fun j => fn_ext fun y hy => ?_)
  have hy' : (𝟙 Y ≫ g) y ∈ M'.U (c'.idx j) := c'.le j hy
  rw [GlobalTheory.SecTwist.gs_pullSec c' _ (𝟙 Y) y j hy, GlobalTheory.SecTwist.gs_pullSec c s (𝟙 Y ≫ g) y _ hy',
    Category.id_comp, hh, hidx j]

theorem gs_liftHom {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} {Z : Scheme.{0}}
    (f : Z ⟶ (T ⊗ A).left) (z : Z) (W : (T ⊗ A).left.Opens) (hz : f z ∈ W) (r : Γ(T.left, ⊤)) :
    gs f z W (liftHom A W r) = gs (f ≫ (fst T A).left) z ⊤ r :=
  (gs_res f z le_top hz _).trans (gs_pull f (fst T A).left z ⊤ trivial _)

def pullLin {S S' Z : Scheme.{0}} (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A'] (L : LB A.left)
    (L' : LB A'.left) (k k' : ℤ) (y : Z ⟶ S) (x : Z ⟶ S') {h : (Over.mk x ⊗ A').left ⟶ (Over.mk y ⊗ A).left}
    (c : ChartPull (LPow A' L' k' (Over.mk x)) (LPow A L k (Over.mk y)) h)
    (hfst : h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) A').left) :
    SecM A L k (Over.mk y) →ₗ[Γ(Z, ⊤)] SecM A' L' k' (Over.mk x) where
  toFun m := SecM.ofSec A' (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m))
  map_add' m₁ m₂ := Subtype.ext (funext fun i => fn_ext fun z hz => by
    have hz' : (𝟙 _ ≫ h) z ∈ (LPow A L k (Over.mk y)).U (c.idx i) := c.le i hz
    show gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A (m₁ + m₂))).f i) =
      gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A m₁)).f i +
        (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m₂)).f i)
    rw [gs_add _ z _ hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz,
      GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz]
    exact gs_add _ z _ hz' _ _)
  map_smul' r m := Subtype.ext (funext fun i => fn_ext fun z hz => by
    have hz' : (𝟙 _ ≫ h) z ∈ (LPow A L k (Over.mk y)).U (c.idx i) := c.le i hz
    show gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A (r • m))).f i) =
      gs (𝟙 _) z _ (liftHom A' _ r * (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m)).f i)
    rw [gs_mul _ z _ hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz]
    refine (gs_mul _ z _ hz' (liftHom A _ r) _).trans (congrArg (· * _) ?_)
    rw [gs_liftHom A _ z _ hz' r, gs_liftHom A' (𝟙 _) z _ hz r, Category.assoc, hfst])

theorem li_span_map {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] {I : Type*} (E : M ≃ₗ[R] M') (v : I → M) (hli : LinearIndependent R v)
    (hsp : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent R (E ∘ v) ∧ Submodule.span R (Set.range (E ∘ v)) = ⊤ := by
  refine ⟨hli.map' E.toLinearMap E.ker, ?_⟩
  rw [Set.range_comp, ← E.coe_toLinearMap, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]

theorem bases_transfer : ∀ {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (L : LB A.left), L.IsLB → ∀ (k : ℤ) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S) (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left) (hc : ∀ _ : Fin 1, (snd (Over.mk x) Ag).left ≫ φ = h ≫ (snd (Over.mk y) A).left), IsIso h → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → ∀ (m : ℕ) (b : Fin m → LB.Sec (LPow A L k (Over.mk y))) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) k (Over.mk x))), (∀ i, b' i = GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left) (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc) (b i)) → LinearIndependent Γ((Over.mk y).left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) → Submodule.span Γ((Over.mk y).left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) = ⊤ → LinearIndependent Γ((Over.mk x).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) ∧ Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) = ⊤ := by
  intro S S' A _ Ag _ φ L _ k R _ x y h hc _ hfst m b b' hb' hli hsp
  let c := chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left)
    (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc
  have hc' : ∀ _ : Fin 1, inv h ≫ (snd (Over.mk x) Ag).left ≫ φ = (snd (Over.mk y) A).left := fun _ => by
    rw [hc 0, IsIso.inv_hom_id_assoc]
  let c' := chartPullUnLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left)
    (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) (inv h) hc'
  have hfst' : inv h ≫ (fst (Over.mk x) Ag).left = (fst (Over.mk y) A).left := by
    rw [← hfst, IsIso.inv_hom_id_assoc]
  let F := pullLin A Ag L (L.pull φ) k k y x c hfst
  let G := pullLin Ag A (L.pull φ) L k k x y c' hfst'
  have GF : ∀ s : LB.Sec (LPow A L k (Over.mk y)),
      GlobalTheory.SecTwist.pullSec c' (GlobalTheory.SecTwist.pullSec c s) = s :=
    pullSec_pullSec c' c (IsIso.inv_hom_id h) (fun _ => rfl)
  have FG : ∀ s : LB.Sec (LPow Ag (L.pull φ) k (Over.mk x)),
      GlobalTheory.SecTwist.pullSec c (GlobalTheory.SecTwist.pullSec c' s) = s :=
    pullSec_pullSec c c' (IsIso.hom_inv_id h) (fun _ => rfl)
  let E : SecM A L k (Over.mk y) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)] SecM Ag (L.pull φ) k (Over.mk x) :=
    { F with
      invFun := G
      left_inv := fun n => congrArg (SecM.ofSec A) (GF (SecM.toSec A n))
      right_inv := fun n => congrArg (SecM.ofSec Ag) (FG (SecM.toSec Ag n)) }
  have hv : (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) =
      E ∘ fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y)) :=
    funext fun i => by rw [hb' i]; rfl
  have key := li_span_map E _ hli hsp
  rw [← hv] at key
  exact key

end GlobalTheory.SecBasisTransfer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionBasesTransferTotalSpaceIsoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sectionBases_transfer_totalSpaceIso : ∀ {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (L : LB A.left), L.IsLB → ∀ (k : ℤ) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S) (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left) (hc : ∀ _ : Fin 1, (snd (Over.mk x) Ag).left ≫ φ = h ≫ (snd (Over.mk y) A).left), IsIso h → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → ∀ (m : ℕ) (b : Fin m → LB.Sec (LPow A L k (Over.mk y))) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) k (Over.mk x))), (∀ i, b' i = GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left) (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc) (b i)) → LinearIndependent Γ((Over.mk y).left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) → Submodule.span Γ((Over.mk y).left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) = ⊤ → LinearIndependent Γ((Over.mk x).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) ∧ Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) = ⊤ := by
  first | (exact @GlobalTheory.SecBasisTransfer.bases_transfer) | (exact GlobalTheory.SecBasisTransfer.bases_transfer) | (intros; apply GlobalTheory.SecBasisTransfer.bases_transfer  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBaseChangeStableSectionBasis

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.HomFixLocBasis

theorem isIso_compare : ∀ {S S' : Scheme.{0}} (u : S' ⟶ S) (A : Over S) (Ag : Over S') (φ : Ag.left ⟶ A.left), IsPullback φ Ag.hom A.hom u → ∀ (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S), x ≫ u = y → ∀ (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left), h ≫ (snd (Over.mk y) A).left = (snd (Over.mk x) Ag).left ≫ φ → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → IsIso h := by
  intro S S' u A Ag φ hφ R _ x y hxy h h1 h2
  subst hxy
  have P := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (Over.mk x)).paste_horiz hφ
  have Q : IsPullback (snd (Over.mk (x ≫ u)) A).left (fst (Over.mk (x ≫ u)) A).left A.hom (x ≫ u) :=
    GlobalTheory.AbLaw.SecBC.isPullback_snd A (Over.mk (x ≫ u))
  have P' : IsPullback ((snd (Over.mk x) Ag).left ≫ φ) (fst (Over.mk x) Ag).left A.hom (x ≫ u) := P
  have e : h = (P'.isoIsPullback _ _ Q).hom :=
    Q.hom_ext (by rw [h1]; exact (IsPullback.isoIsPullback_hom_fst _ _ P' Q).symm) (by rw [h2]; exact (IsPullback.isoIsPullback_hom_snd _ _ P' Q).symm)
  rw [e]
  infer_instance

theorem exists_basicOpen_le {Rg : Type} [CommRing Rg] (V : (Sp Rg).Opens) (p : Sp Rg) (hpV : p ∈ V) :
    ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧
      ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Rg)) ⊆ (V : Set (Sp Rg))) := by
  have hVo : IsOpen (X := PrimeSpectrum Rg) (V : Set (Sp Rg)) := V.isOpen
  have hpV' : (p : PrimeSpectrum Rg) ∈ (V : Set (Sp Rg)) := hpV
  obtain ⟨W, ⟨f, rfl⟩, h1, h2⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := Rg)).exists_subset_of_mem_open
    (a := (p : PrimeSpectrum Rg)) (u := ((V : Set (Sp Rg)) : Set (PrimeSpectrum Rg))) hpV' hVo
  exact ⟨f, h1, h2⟩

theorem exists_factor_away {Rg : Type} [CommRing Rg] (V : (Sp Rg).Opens) (f g : Rg)
    (hfV : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Rg)) ⊆ (V : Set (Sp Rg)))
    (hg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ∃ uV : Sp (Localization.Away g) ⟶ V.toScheme, uV ≫ V.ι = spMap (algebraMap Rg (Localization.Away g)) := by
  have hu : Set.range (spMap (algebraMap Rg (Localization.Away g))) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have h1 : PrimeSpectrum.comap (algebraMap Rg (Localization.Away g)) x ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum Rg)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact ⟨x, rfl⟩
    exact hfV (hg h1)
  exact ⟨_, IsOpenImmersion.lift_fac V.ι _ hu⟩

theorem secBasis_of_factor {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (hL : L.IsLB) (k : ℕ) (V : (Sp Rg).Opens) (m : ℕ)
    (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)))
    (hb : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) V).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤)
    {S' : Scheme.{0}} (u : S' ⟶ Sp Rg) (uV : S' ⟶ V.toScheme) (huV : uV ≫ V.ι = u)
    (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (hφ : IsGrpPullback Ag A u φ) :
    ∃ (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver S') ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S') ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤ := by
  have hAgw : φ ≫ A.hom = Ag.hom ≫ u := hφ.1.w
  have hw : ((snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ) ≫ A.hom =
      ((fst (overRes (T := baseOver S') ⊤) Ag).left ≫ (⊤ : S'.Opens).ι ≫ uV) ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by
    have e := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (overRes (T := baseOver S') ⊤)).w
    simp only [Category.assoc, hAgw]
    rw [← Category.assoc, e]
    simp [overRes, baseOver, huV]
  obtain ⟨H, hH1, hH2⟩ : ∃ H : (overRes (T := baseOver S') ⊤ ⊗ Ag).left ⟶ (overRes (T := baseOver (Sp Rg)) V ⊗ A).left,
      H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left = (snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ ∧
      H ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left = (fst (overRes (T := baseOver S') ⊤) Ag).left ≫ (⊤ : S'.Opens).ι ≫ uV :=
    ⟨_, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_fst _ _ hw, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_snd _ _ hw⟩
  have hc : ∀ _ : Fin 1, (snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ = H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left :=
    fun _ => hH1.symm
  refine ⟨fun i => GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left)
    (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i), ?_⟩
  intro R _ t b' hb'
  obtain ⟨t', ht'⟩ : ∃ t' : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) V).left, t' = t ≫ (⊤ : S'.Opens).ι ≫ uV := ⟨_, rfl⟩
  choose b'' hb'' using fun i => GlobalTheory.AbLaw.SecBC.exists_pullSec A L (k : ℤ) (homAt t') (b i)
  have hB := hb R t' b'' hb''
  have hxy : (t ≫ (overRes (T := baseOver S') ⊤).hom) ≫ u = t' ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by
    rw [ht']
    simp [overRes, baseOver, huV]
  have hw2 : ((snd (baseAt t) Ag).left ≫ φ) ≫ A.hom = (fst (baseAt t) Ag).left ≫ (baseAt t').hom := by
    have e := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (baseAt t)).w
    simp only [Category.assoc, hAgw]
    rw [← Category.assoc, e]
    simp [baseAt, overRes, baseOver, ht', huV]
  obtain ⟨h, hh1, hh2⟩ : ∃ h : (baseAt t ⊗ Ag).left ⟶ (baseAt t' ⊗ A).left,
      h ≫ (snd (baseAt t') A).left = (snd (baseAt t) Ag).left ≫ φ ∧
      h ≫ (fst (baseAt t') A).left = (fst (baseAt t) Ag).left :=
    ⟨_, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_fst _ _ hw2, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_snd _ _ hw2⟩
  have hc' : ∀ _ : Fin 1, (snd (baseAt t) Ag).left ≫ φ = h ≫ (snd (baseAt t') A).left := fun _ => hh1.symm
  refine GlobalTheory.T.sectionBases_transfer_totalSpaceIso A Ag φ L hL (k : ℤ) R _ _ h hc' (isIso_compare u A Ag φ hφ.1 R _ _ hxy h hh1 hh2) hh2 m b'' b' ?_ hB.1 hB.2
  have hcomp : (homAt t ▷ Ag).left ≫ H = h ≫ (homAt t' ▷ A).left := by
    apply (GlobalTheory.AbLaw.SecBC.isPullback_snd A (overRes (T := baseOver (Sp Rg)) V)).hom_ext
    · rw [Category.assoc, hH1, Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, ← Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, hh1]
    · have e1 := GlobalTheory.AbLaw.SecBC.fst_eq Ag (homAt t)
      have e2 := GlobalTheory.AbLaw.SecBC.fst_eq A (homAt t')
      calc ((homAt t ▷ Ag).left ≫ H) ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left
            = ((homAt t ▷ Ag).left ≫ (fst (overRes (T := baseOver S') ⊤) Ag).left) ≫ (⊤ : S'.Opens).ι ≫ uV := by
              rw [Category.assoc, hH2, Category.assoc]
        _ = (fst (baseAt t) Ag).left ≫ t ≫ (⊤ : S'.Opens).ι ≫ uV := by
              rw [e1]
              try simp [homAt]
        _ = (h ≫ (homAt t' ▷ A).left) ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left := by
              rw [Category.assoc, e2, reassoc_of% hh2, ht']
              try simp [homAt]
  intro i
  apply GlobalTheory.SecTwist.sec_ext_loc
  intro y
  obtain ⟨j, hj⟩ : ∃ j, y ∈ (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j :=
    exists_chart (LB.isLB_linComb (LB.isLB_pull hL φ) _ _ : (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).IsLB) y
  refine ⟨j, hj, ?_⟩
  have hj1 := chart_le_res Ag (L.pull φ) (homAt t ▷ Ag) (whiskerRight_snd _ _) (k : ℤ) j hj
  have hj2 : h y ∈ (LPow A L (k : ℤ) (baseAt t')).U (fun k => j k PUnit.unit) := by
    have := (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
      (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc').le j hj
    exact this
  have lhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j) ((b' i).f j) =
      gs ((homAt t ▷ Ag).left ≫ H) y ((LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit))
        ((b i).f (fun k => j k PUnit.unit)) := by
    rw [hb' i j, GlobalTheory.AbLaw.SecBC.gs_rp _ _ (𝟙 _) y hj, Category.id_comp]
    exact GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left)
      (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i) (homAt t ▷ Ag).left y j hj1
  have rhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j)
      ((GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
        (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i)).f j) =
      gs (h ≫ (homAt t' ▷ A).left) y ((LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit))
        ((b i).f (fun k => j k PUnit.unit)) := by
    have e1 := GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
        (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i) (𝟙 _) y j hj
    rw [Category.id_comp] at e1
    refine e1.trans ?_
    erw [hb'' i (fun k => j k PUnit.unit)]
    exact GlobalTheory.AbLaw.SecBC.gs_rp _ _ h y hj2 _
  rw [lhs, rhs, hcomp]

theorem exists_basicOpen_secBasis : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ k : ℕ, 1 ≤ k → ∀ p : Sp Rg, ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧ ∀ g : Rg, PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f → ∀ (Ag : Over (Sp (Localization.Away g))) [GrpObj Ag] [IsCommMonObj Ag] (φ : Ag.left ⟶ A.left), IsGrpPullback Ag A (spMap (algebraMap Rg (Localization.Away g))) φ → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver (Sp (Localization.Away g))) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp (Localization.Away g))) ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤) := by
  intro Rg _ _ A _ _ L hAb hL hRig hAmp k hk p
  obtain ⟨V, hpV, m, b, hb⟩ := GlobalTheory.AmpleSecBC.secBaseChange_relAmple (Sp Rg) A L hAb hL hRig hAmp k hk p
  have hx := exists_basicOpen_le (Rg := Rg) V p hpV
  refine ⟨hx.choose, hx.choose_spec.1, fun g hg Ag _ _ φ hφ => ⟨m, ?_⟩⟩
  have hu := exists_factor_away V _ g hx.choose_spec.2 hg
  exact secBasis_of_factor A L hL k V m b hb _ hu.choose hu.choose_spec Ag φ hφ

end GlobalTheory.HomFixLocBasis
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBaseChangeStableSectionBasisStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out


theorem _root_.GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ k : ℕ, 1 ≤ k → ∀ p : Sp Rg, ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧ ∀ g : Rg, PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f → ∀ (Ag : Over (Sp (Localization.Away g))) [GrpObj Ag] [IsCommMonObj Ag] (φ : Ag.left ⟶ A.left), IsGrpPullback Ag A (spMap (algebraMap Rg (Localization.Away g))) φ → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver (Sp (Localization.Away g))) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp (Localization.Away g))) ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤) := by
  first | exact @GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis | exact GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis | (intros; apply GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis <;> assumption)
end
end
