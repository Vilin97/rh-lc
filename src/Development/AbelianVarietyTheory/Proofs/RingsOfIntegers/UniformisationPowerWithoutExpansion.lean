module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvenAlong
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CubBoxVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GmCharPow
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SquareRes
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymBox
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BoxSymIsSymmetry
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LcgLinCombEqProd
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullGenBoxGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxIso

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowerThickIso

section General

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull gm_div gm_linComb gm_pull_g gm_self mem_pull PGen isGen_iff glue_unit
  exists_chart)

variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'}
  {h : Fin j → (Ge' ⟶ Ge)}

theorem gm_box_g {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z) (a b : Fin j → M.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i))
    (hb : ∀ i, pr i (ψ z) ∈ M.U (b i)) :
    gm ψ z (LB.wchart M pr a ⊓ LB.wchart M pr b) ((LB.LinComb M pr (fun _ => 1)).g a b) =
      ∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i)) :=
  (gm_linComb M pr (fun _ => 1) ψ z a b (Set.mem_iInter.2 ha) (Set.mem_iInter.2 hb)).trans
    (Finset.prod_congr rfl fun _ _ => zpow_one _)

theorem bw_change {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} (hw : w.IsGen) {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z)
    (a b : Fin j → M.ι) (k k' : M'.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i)) (hb : ∀ i, pr i (ψ z) ∈ M.U (b i))
    (hk : ψ z ∈ M'.U k) (hk' : ψ z ∈ M'.U k') :
    bw w ψ z a k = (∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i))) *
      (gm ψ z _ (M'.g k k'))⁻¹ * bw w ψ z b k' := by
  have hm : ψ z ∈ LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k') :=
    ⟨⟨Set.mem_iInter.2 ha, hk⟩, Set.mem_iInter.2 hb, hk'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k'))) (hw (a, k) (b, k'))
  have e' := (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (a, k) (b, k') hm) (gm_res ψ z _ hm _))))
  rw [← gm_box_g ψ z a b ha hb]
  exact e'

def germ (pG' : Ge' ⟶ B') (h : Fin j → (Ge' ⟶ Ge)) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    (we : LB.Iso (L.pull fG) (M.pull pG)) {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι)
    (jL : Fin j → L.ι) : (Z.presheaf.stalk z)ˣ :=
  (bw w (r ≫ pG') z jM jM')⁻¹ * ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i)

theorem germ_change (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : Fin j → M.ι) (jM' kM' : M'.ι) (jL kL : Fin j → L.ι)
    (a₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (jL i))
    (b₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (kM i)) (b₂ : pG' (r z) ∈ M'.U kM') (b₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (kL i)) :
    germ pG' h w we r z jM jM' jL =
      gm (r ≫ pG') z _ (M'.g jM' kM') *
        (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        germ pG' h w we r z kM kM' kL := by
  have p₁ : ∀ i, pG (h i (r z)) = pr i (pG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₁ i).symm
  have p₂ : ∀ i, fG (h i (r z)) = prG i (fG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₂ i)
  have a := bw_change hw (r ≫ pG') z jM kM jM' kM' a₁ b₁ a₂ b₂
  have c : ∀ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) =
      gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i)) *
        (gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i) := fun i => by
    have c₃ : fG (h i (r z)) ∈ L.U (jL i) := p₂ i ▸ a₃ i
    have d₃ : fG (h i (r z)) ∈ L.U (kL i) := p₂ i ▸ b₃ i
    have c₁ : pG (h i (r z)) ∈ M.U (jM i) := p₁ i ▸ a₁ i
    have d₁ : pG (h i (r z)) ∈ M.U (kM i) := p₁ i ▸ b₁ i
    have c := hwe Z (r ≫ h i) z (jM i) (kM i) (fun _ => jL i) (fun _ => kL i) c₁ d₁ (mem_pull.2 c₃) (mem_pull.2 d₃)
    rw [gm_pull_g L fG (r ≫ h i) z (fun _ => jL i) (fun _ => kL i) (mem_pull.2 c₃) (mem_pull.2 d₃),
      Category.assoc, Category.assoc, ← e₁, e₂] at c
    rw [Category.assoc, Category.assoc]
    exact c
  unfold germ
  rw [a, Finset.prod_congr rfl fun i _ => c i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  generalize (∏ i, gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i))) = A
  generalize (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i))) = C
  generalize gm (r ≫ pG') z _ (M'.g jM' kM') = A'
  generalize bw w (r ≫ pG') z kM kM' = P
  generalize (∏ i, Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i)) = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    (jM' : M'.ι) (jL : Fin j → L.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι), (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) →
        pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        gm r z _ s = germ pG' h w we r z jM jM' jL := by
  have p₁ : ∀ i x, pG (h i x) = pr i (pG' x) := fun i x => congrArg (fun g => g x) (e₁ i).symm
  have p₂ : ∀ i x, fG (h i x) = prG i (fG' x) := fun i x => congrArg (fun g => g x) (e₂ i)
  obtain ⟨W, hW⟩ : ∃ W : (Fin j → M.ι) → Ge'.Opens, ∀ a x, x ∈ W a ↔
      (∀ i, pr i (pG' x) ∈ M.U (a i)) ∧ pG' x ∈ M'.U jM' ∧ ∀ i, prG i (fG' x) ∈ L.U (jL i) :=
    ⟨fun a => pG' ⁻¹ᵁ LB.wchart M pr a ⊓ (pG' ⁻¹ᵁ M'.U jM' ⊓ fG' ⁻¹ᵁ LB.wchart L prG jL),
      fun _ _ => and_congr Set.mem_iInter (and_congr Iff.rfl Set.mem_iInter)⟩
  have l₀ : ∀ a, W a ≤ (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL) :=
    fun a x hx => ⟨mem_pull.2 ((hW a x).1 hx).2.1, mem_pull.2 (Set.mem_iInter.2 ((hW a x).1 hx).2.2)⟩
  have l₁ : ∀ a, W a ≤ pG' ⁻¹ᵁ (LB.wchart M pr a ⊓ M'.U jM') := fun a x hx =>
    ⟨Set.mem_iInter.2 ((hW a x).1 hx).1, ((hW a x).1 hx).2.1⟩
  have l₂ : ∀ a i, W a ≤ h i ⁻¹ᵁ ((M.pull pG).U (fun _ => a i) ⊓ (L.pull fG).U (fun _ => jL i)) := fun a i x hx =>
    ⟨mem_pull.2 ((p₁ i x).symm ▸ ((hW a x).1 hx).1 i), mem_pull.2 ((p₂ i x).symm ▸ ((hW a x).1 hx).2.2 i)⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ a, Γ(Ge', W a)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (a : Fin j → M.ι), r z ∈ W a →
      gm r z (W a) (u a) = germ pG' h w we r z a jM' jL :=
    ⟨fun a => (res (l₁ a) (pullU pG' _ (w.s (a, jM'))))⁻¹ *
        ∏ i, res (l₂ a i) (pullU (h i) _ (we.s (fun _ => a i, fun _ => jL i))),
      fun Z r z a hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z (l₁ a) hz _).trans (gm_pull r pG' z _ (l₁ a hz) _)))) ((map_prod _ _ _).trans
          (Finset.prod_congr rfl fun i _ =>
            (gm_res r z (l₂ a i) hz _).trans (gm_pull r (h i) z _ (l₂ a i hz) _))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      choose a ha using fun i => exists_chart hM (pr i (pG' x))
      exact TopologicalSpace.Opens.mem_iSup.2
        ⟨a, (hW a x).2 ⟨ha, mem_pull.1 hx.1, Set.mem_iInter.1 (mem_pull.1 hx.2)⟩⟩) u
    (fun a a' x hx => by
      have h₁ := (hW a x).1 hx.1
      have h₂ := (hW a' x).1 hx.2
      have k := germ_change e₁ e₂ hw hwe (𝟙 Ge') x a a' jM' jM' jL jL h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
      rw [gm_self hM' (𝟙 Ge' ≫ pG') x h₁.2.1, Finset.prod_eq_one fun i _ =>
        gm_self hL ((𝟙 Ge' ≫ fG') ≫ prG i) x (h₁.2.2 i), inv_one, _root_.one_mul, _root_.one_mul] at k
      exact (hu _ (𝟙 Ge') x a hx.1).trans (k.trans (hu _ (𝟙 Ge') x a' hx.2).symm))
  refine ⟨s, fun Z r z jM a₁ a₂ a₃ => ?_⟩
  have hz := (hW jM (r z)).2 ⟨a₁, a₂, a₃⟩
  exact (gm_res r z (l₀ jM) hz s).symm.trans ((congrArg (gm r z (W jM)) (hs jM)).trans (hu Z r z jM hz))

theorem exists_box_iso (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen)
    (hwe : we.IsGen) :
    ∃ we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι) (jL : Fin j → L.ι),
        (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) → pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        bw w (r ≫ pG') z jM jM' * Geo.Tor.gw we' r z jM' (fun _ => jL) =
          ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) := by
  rw [isGen_iff] at hwe
  choose s hs using exists_unit hM hM' hL e₁ e₂ hw hwe
  refine ⟨⟨fun p => s (p.1 PUnit.unit) (p.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, fun Z r z jM jM' jL a₁ a₂ a₃ => ?_⟩
  · intro Z r z l l' k k' a₂ b₂ a₄ b₄
    choose a ha using fun i => exists_chart hM (pr i (pG' (r z)))
    have a₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 a₄)
    have b₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k' PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 b₄)
    have c := germ_change e₁ e₂ hw hwe r z a a l l' _ _ ha a₂ a₄' ha b₂ b₄'
    rw [← hs l _ Z r z a ha a₂ a₄', ← hs l' _ Z r z a ha b₂ b₄', ← gm_box_g (r ≫ fG') z _ _ a₄' b₄'] at c
    rw [gm_pull_g (LB.LinComb L prG (fun _ => 1)) fG' r z k k' a₄ b₄]
    exact c
  · exact (congrArg (bw w (r ≫ pG') z jM jM' * ·) (hs jM' jL Z r z jM a₁ a₂ a₃)).trans
      (mul_inv_cancel_left _ _)

end General

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (e : ℕ) (g : GtCoord I D.toPre e G) (g' : GtCoord I D'.toPre e G'), (∀ i, g'.pG.left ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ g.pG.left) → ∀ (L : LB G.left), L.IsLB → ∀ w : LB.Iso (L.pull (fstG I e G).left) (D.toPre.P.L.pull g.pG.left), w.IsGen → ∃ w' : LB.Iso ((boxLB L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : Fin j → L.ι), (∀ i, (pD.pw.pr i).left (g'.pG.left (r z)) ∈ D.toPre.P.L.U (jM i)) → g'.pG.left (r z) ∈ D'.toPre.P.L.U jM' → (∀ i, (pG.pr i).left ((fstG I e G').left (r z)) ∈ L.U (jL i)) → bw pD.w (r ≫ g'.pG.left) z jM jM' * Geo.Tor.gw w' r z jM' (fun _ => jL) = ∏ i, Geo.Tor.gw w (r ≫ ((Over.pullback (thick R I e)).map (pG.pr i)).left) z (jM i) (fun _ => jL i) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG e g g' hq L hL w hw
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  exact exists_box_iso (Ge := (thickObj R I e G).left) (Ge' := (thickObj R I e G').left) (h := rhoE I pG e)
    (pG := g.pG.left) (pG' := g'.pG.left) (fG := fGl I G e) (fG' := fGl I G' e)
    D.toPre.P.isLB D'.toPre.P.isLB hL hq hρ pD.w w pD.w_gen hw

end GlobalTheory.PowerThickIso
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsoOfIsPowGrp

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
noncomputable def chartPullPullLinComb {X X' Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (pr : K → (X' ⟶ X)) (ε : K → ℤ) (F : Y ⟶ X') (g : Z ⟶ X) (p : K → (Y ⟶ Z))
    (hc : ∀ k, p k ≫ g = F ≫ pr k) :
    ChartPull ((LB.LinComb L pr ε).pull F) (LB.LinComb (L.pull g) p ε) (𝟙 Y) :=
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L pr ε).pull F).U J ≤
      LB.wchart (L.pull g) p (fun k _ => J PUnit.unit k) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => by
      have h1 : (F ≫ pr k) y ∈ L.U (J PUnit.unit k) :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) k
      rw [← hc k] at h1
      exact h1
  { idx := fun J k _ => J PUnit.unit k
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (LB.LinComb L pr ε) F (𝟙 Y) y J J' hj hj').trans ?_
      refine (gm_linComb L pr ε (𝟙 Y ≫ F) y _ _ (Set.mem_iInter.1 hj PUnit.unit)
        (Set.mem_iInter.1 hj' PUnit.unit)).trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull g) p ε (𝟙 Y) y _ _ (le J hj) (le J' hj')).symm)
      refine Eq.trans ?_ (gm_pull_g L g (𝟙 Y ≫ p k) y _ _ (Set.mem_iInter.1 (le J hj) k)
        (Set.mem_iInter.1 (le J' hj') k)).symm
      rw [Category.assoc, Category.assoc, hc] }

theorem isMonHom_of_isPowGrp {S : Scheme.{0}} {H G' G : Over S} [GrpObj H] [GrpObj G'] [GrpObj G]
    {j : ℕ} (p : IsPowGrp G' G j) (f : H ⟶ G') (hf : ∀ i, IsMonHom (f ≫ p.pr i)) : IsMonHom f := by
  have ext : ∀ (a b : H ⊗ H ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun a b h => Fan.IsLimit.hom_ext p.lim a b h
  have ext1 : ∀ (a b : 𝟙_ (Over S) ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun a b h => Fan.IsLimit.hom_ext p.lim a b h
  constructor
  · refine ext1 _ _ fun i => ?_
    rw [Category.assoc, (hf i).one_hom, (p.hom i).one_hom]
  · refine ext _ _ fun i => ?_
    rw [Category.assoc, (hf i).mul_hom, Category.assoc, (p.hom i).mul_hom, ← Category.assoc (f ⊗ₘ f),
      tensorHom_comp_tensorHom]

theorem exists_iso_of_isPowGrp {S : Scheme.{0}} {H' H G' G : Over S} [GrpObj H'] [GrpObj H]
    [GrpObj G'] [GrpObj G] {j : ℕ} (q : IsPowGrp H' H j) (p : IsPowGrp G' G j) (e : H ≅ G)
    [IsMonHom e.hom] :
    ∃ e' : H' ≅ G', IsMonHom e'.hom ∧ ∀ i, e'.hom ≫ p.pr i = q.pr i ≫ e.hom := by
  let u : H' ⟶ G' := Fan.IsLimit.lift p.lim fun i => q.pr i ≫ e.hom
  let v : G' ⟶ H' := Fan.IsLimit.lift q.lim fun i => p.pr i ≫ e.inv
  have hu : ∀ i, u ≫ p.pr i = q.pr i ≫ e.hom := fun i => Fan.IsLimit.fac p.lim _ i
  have hv : ∀ i, v ≫ q.pr i = p.pr i ≫ e.inv := fun i => Fan.IsLimit.fac q.lim _ i
  have huv : u ≫ v = 𝟙 H' := Fan.IsLimit.hom_ext q.lim _ _ fun i => by
    change (u ≫ v) ≫ q.pr i = 𝟙 H' ≫ q.pr i
    rw [Category.assoc, hv i, ← Category.assoc, hu i, Category.assoc, e.hom_inv_id, Category.comp_id,
      Category.id_comp]
  have hvu : v ≫ u = 𝟙 G' := Fan.IsLimit.hom_ext p.lim _ _ fun i => by
    change (v ≫ u) ≫ p.pr i = 𝟙 G' ≫ p.pr i
    rw [Category.assoc, hu i, ← Category.assoc, hv i, Category.assoc, e.inv_hom_id, Category.comp_id,
      Category.id_comp]
  refine ⟨⟨u, v, huv, hvu⟩, ?_, hu⟩
  refine isMonHom_of_isPowGrp p _ fun i => ?_
  have : IsMonHom (q.pr i) := q.hom i
  change IsMonHom (u ≫ p.pr i)
  rw [hu i]
  infer_instance


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_gen_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ gen' : (Over.pullback (jK R)).obj G' ≅ A'.A, IsMonHom gen'.hom ∧ (∀ i, gen'.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ ∃ w : LB.Iso (A'.L.pull gen'.hom.left) ((boxLB U.LG.L pG.pr).pull (pullback.fst G'.hom (jK R))), w.IsGen := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U
  have : IsMonHom U.gen.hom := U.gen_hom
  obtain ⟨p', hp'⟩ := isPowGrp_baseChange _ _ (jK R) G' G j pG
  obtain ⟨e', he', hc⟩ := exists_iso_of_isPowGrp p' pA.toIsPowGrp U.gen
  refine ⟨e', he', fun i => by rw [hc i, hp' i], ?_⟩
  obtain ⟨w0, hw0⟩ := U.ext
  have pullCP : ∀ {X Y : Scheme.{0}} (L : LB X) (F : Y ⟶ X), ChartPull (L.pull F) L F := fun L F =>
    { idx := fun J => J PUnit.unit
      le := fun J y hy => (mem_pull (L := L) (F := F) (x := y) (J := J)).1 hy
      g := fun y J J' hj hj' => (gm_pull_g L F (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp]) }
  have hcA : ∀ k, (p'.pr k).left ≫ U.gen.hom.left = e'.hom.left ≫ (pA.pr k).left := fun k => by
    simpa using (congrArg (fun m => m.left) (hc k)).symm
  have hcG : ∀ k, (p'.pr k).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ (pG.pr k).left := fun k => by
    rw [hp' k]
    simp
  have H34 : LBIso (LB.LinComb (A.L.pull U.gen.hom.left) (fun k => (p'.pr k).left) (fun _ => 1))
      (LB.LinComb (U.LG.L.pull (pullback.fst G.hom (jK R))) (fun k => (p'.pr k).left) (fun _ => 1)) :=
    ⟨LB.linCombIso w0 _ _, linCombIso_isGen w0 hw0 _ _⟩
  have HB : LBIso ((boxLB A.L pA.pr).pull e'.hom.left)
      ((boxLB U.LG.L pG.pr).pull (pullback.fst G'.hom (jK R))) :=
    LBIso.chartPull
      (chartPullPullLinComb A.L (fun k => (pA.pr k).left) (fun _ => 1) e'.hom.left U.gen.hom.left
        (fun k => (p'.pr k).left) hcA)
      (chartPullPullLinComb U.LG.L (fun k => (pG.pr k).left) (fun _ => 1) (pullback.fst G'.hom (jK R))
        (pullback.fst G.hom (jK R)) (fun k => (p'.pr k).left) hcG) H34
  have HA : LBIso (A'.L.pull e'.hom.left) ((boxLB A.L pA.pr).pull e'.hom.left) :=
    LBIso.chartPull (pullCP A'.L e'.hom.left) (pullCP _ e'.hom.left) ⟨pA.w, pA.w_gen⟩
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (linComb_isLB _ A.isLB _ _) _)
    (pull_isLB (linComb_isLB _ U.LG.isLB _ _) _) HA HB

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UniformisationPowerWithoutExpansion

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

section Level

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig GlobalTheory.WCub

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

omit [IsDomain R] [IsCommMonObj G] [IsCommMonObj G'] in
theorem rho_fst (pG : IsPowGrp G' G j) (e : ℕ) (i : Fin j) :
    rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := pullback.lift_fst _ _ _

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem thickMap_rho (pG : IsPowGrp G' G j) (e : ℕ) (i : Fin j) :
    thickMap R I e G' ≫ rhoE I pG (e + 1) i = rhoE I pG e i ≫ thickMap R I e G := by
  have : Mono (fGl I G (e + 1)) := mono_fstG I (e + 1) G
  have a : thickMap R I e G ≫ fGl I G (e + 1) = fGl I G e := thickMap_fstG I e G
  have a' : thickMap R I e G' ≫ fGl I G' (e + 1) = fGl I G' e := thickMap_fstG I e G'
  rw [← cancel_mono (fGl I G (e + 1)), Category.assoc, Category.assoc, rho_fst, a, rho_fst, ← Category.assoc, a']

theorem thickMap_pG (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G) (e : ℕ)
    (g₀ : GtCoord I D'.toPre e G') (g₁ : GtCoord I D'.toPre (e + 1) G')
    (h₀ : ∀ i, g₀.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (h₁ : ∀ i, g₁.pG.left ≫ (pD.pw.pr i).left = rhoE I pG (e + 1) i ≫ (U.gt (e + 1)).pG.left) :
    thickMap R I e G' ≫ g₁.pG.left = g₀.pG.left := by
  have h : LevelCompat.thickMapOver I e G' ≫ g₁.pG = g₀.pG := pD.pw.lim.hom_ext fun ⟨i⟩ =>
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (thickMap R I e G' ≫ ·) (h₁ i)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (U.gt (e + 1)).pG.left) (thickMap_rho pG e i)).trans
        ((Category.assoc _ _ _).trans ((congrArg (rhoE I pG e i ≫ ·) (U.gt_q e)).trans (h₀ i).symm))))))
  exact congrArg (fun z => z.left) h

variable (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G)
    (e : ℕ) (g' : GtCoord I D'.toPre e G')
    (hq : ∀ i, g'.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (w' : LB.Iso ((boxLB U.LG.L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left))
    (Q : BoxSquare (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) pD.w (U.w e) w' (rhoE I pG e))
include hq Q

theorem rig_level : RigAlong (T := (thickObj R I e G').left) w' (eSec (thickObj R I e G')) (thick R I e)
    (boxRig pG U.LG.L U.LG.rig) D'.toPre.rig := by
  obtain ⟨b, b₁, b₂⟩ := pD.w_rig
  exact rig_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q (rho_fst pG e) hq U.LG.rigGen (U.w_rig e)
    (fun i => by
      have := pG.hom i
      exact BoxSymmetry.eSec_comp_hom ((Over.pullback (thick R I e)).map (pG.pr i)))
    (eSec_fstG I e G) (eSec_pG I (U.gt e)) (eSec_pG I g')
    (fun i _ => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).e_comm) b b₁ b₂

theorem even_level (hG : GlobalFnsSt) : EvenAlong (T := (thickObj R I e G').left) w' (ι[thickObj R I e G']).left
    (boxSym pG U.LG.L U.symG) D'.toPre.sym := by
  have := g'.q_hom
  have := (U.gt e).q_hom
  exact even_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q (rho_fst pG e) hq
    (fun i => by
      have := pG.hom i
      exact EvenPull.inv_left_comp ((Over.pullback (thick R I e)).map (pG.pr i)))
    (EvenPull.inv_fst _ G) (EvenPull.inv_hom_fst _ _ (U.gt e).q) (EvenPull.inv_hom_fst _ _ g'.q) (inv_pr pG)
    U.symG U.symG_gen D.toPre.sym D'.toPre.sym
    (fun y J J' hJ hJ' => PsiEvenBox.sym_box hG pD g'.pG.left y hJ hJ') (U.w_even e)

end Level


open GlobalTheory.WCub in

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ (U' : UnifPre I D' A' G') (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) := by
  intro hG R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U
  obtain ⟨gen, gen_hom, gen_pr, ext⟩ := exists_gen_pow R I j D D' A A' G G' pD pA pG U
  choose gt q_pr t_pr using fun e => GlobalTheory.PowTorusCoord.main hG R I j D D' A A' G G' pD pA pG e (U.gt e)
  have hq : ∀ e i, (gt e).pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left :=
    fun e i => (t_pr e 0).choose i 2
  choose w w_gen Q using fun e => PowerThickIso.main R I j D D' A A' G G' pD pA pG e (U.gt e) (gt e) (hq e)
    U.LG.L U.LG.isLB (U.w e) (U.w_gen e)
  have hL := boxIsLB _ G' G j pG U.LG.L U.LG.isLB
  have hr := boxRigIsGen _ G' G j pG U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen
  obtain ⟨c, hc⟩ := boxCubical _ G' G j pG U.LG U.cubG hL hr
  obtain ⟨s₁, s₂⟩ := boxSym_isSymmetry _ G' G j pG U.LG.L U.symG U.LG.isLB U.symG_gen U.symG_rig
  have gq := fun e => thickMap_pG pD pG U e (gt e) (gt (e + 1)) (hq e) (hq (e + 1))
  refine ⟨{
      smooth := (PowGrp.powers _ G' G j pG).1 U.smooth
      separated := (PowGrp.powers _ G' G j pG).2.1 U.separated
      gen := gen
      gen_hom := gen_hom
      LG := ⟨boxLB U.LG.L pG.pr, boxRig pG U.LG.L U.LG.rig, hL, hr⟩
      cubG := c
      symG := boxSym pG U.LG.L U.symG
      symG_gen := s₁
      symG_rig := s₂
      ext := ext
      gt := gt
      gt_q := gq
      gt_t := fun e χ => corr_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left)
        (T₁ := (thickObj R I (e + 1) G).left) (T₁' := (thickObj R I (e + 1) G').left)
        D.toPre.P.isLB D'.toPre.P.isLB pD.w (thickMap_rho pG e) (t_pr e χ).choose
        (t_pr (e + 1) χ).choose (LevelCompat.thickMap_Oφ (gt e) (gt (e + 1)) (gq e) χ) (t_pr e χ).choose_spec
        (t_pr (e + 1) χ).choose_spec (fun i => U.gt_t e _)
      w := w
      w_gen := w_gen
      w_rig := fun e => rig_level pD pG U e (gt e) (hq e) (w e) (Q e)
      w_even := fun e => even_level pD pG U e (gt e) (hq e) (w e) (Q e) hG
      w_cub := fun e T x jL jM _ cM => (clause_iff (tri (thick R I e) (gt e).pG x) (tri (thick R I e) (fstG I e G') x)
        (fun k : thK => (psum (thickObj R I e G') x k.down).left) _ _ _ (D'.toPre.cub.t.s jM) (c.t.s jL)
        (fun k => (w e).s (fun _ => jM k, fun _ => jL k)) thε).2 fun y hB hL _ => by
          rw [hc]
          exact cub_box hG pD pG U e (gt e) (hq e) (w e) (Q e) T x jL jM cM y hB hL
      w_compat := fun e => compat_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left)
        (T₁ := (thickObj R I (e + 1) G).left) (T₁' := (thickObj R I (e + 1) G').left)
        D.toPre.P.isLB (Q e) (Q (e + 1)) (U.w_compat e) (UnifPullRig.thickMap_fstG I e G) (U.gt_q e)
        (UnifPullRig.thickMap_fstG I e G') (gq e) (rho_fst pG e) (hq e) (thickMap_rho pG e) },
    Geo.Tor.idIso _, gen_pr, Geo.Tor.idIso_isGen hL, ?_, q_pr, t_pr, fun e jNM jM' jL' jNL => ?_⟩
  · exact idIso_rig U.LG.isLB U.LG.rig (fun i _ => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).e_comm) hr
  · exact square_res (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D'.toPre.P.isLB (w_gen e) (Q e)
      jNM jM' jL' jNL _ _ _ _ _

end GlobalTheory.PowUnif
end
end
end
