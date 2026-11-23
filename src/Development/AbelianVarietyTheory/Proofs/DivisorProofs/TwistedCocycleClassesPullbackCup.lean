module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullAwChainsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaceSubMid
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GagaLineGeneratorEmbedding

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.PBFc.AWCross

theorem idc_eq (M a : ℕ) (h : 0 + a ≤ M) : idc M a = SimplexCategory.subinterval 0 a h :=
  hom_ext_val _ _ fun v => by
    rw [sub_val]
    change min M (v : ℕ) = (v : ℕ) + 0
    have := v.2
    omega

theorem backc_eq (M a b : ℕ) (h : a + b ≤ M) : backc M a b = SimplexCategory.subinterval a b h :=
  hom_ext_val _ _ fun v => by
    rw [sub_val]
    change min M (a + (v : ℕ)) = (v : ℕ) + a
    have := v.2
    omega

variable {R : Type} [CommRing R]

theorem evT_of_eq {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ : Cochain (totChains R X) K n) (a b : ℕ) (t s : ℤ)
    (ht : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (-(a : ℤ), -(b : ℤ)) = t)
    (h : t + n = s) (U : Scheme.{0}) (y : BSx X a b U) :
    Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) t ht ≫
      γ.v t s h) (freeGen R _ U y) =
    evT γ a b s (by simp only [ComplexShape.π_def] at ht; push_cast; omega) U y := by
  obtain rfl : t = -((a + b : ℕ) : ℤ) := by simp only [ComplexShape.π_def] at ht; push_cast; omega
  rfl

theorem map_comp_apply' {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (y : Sec F U) :
    Sec.map (f ≫ g) y = Sec.map g (Sec.map f y) := rfl

theorem mapHom_apply' (F G : Shv R) {U : Scheme.{0}} (y : Sec F U) (φ : F ⟶ G) : mapHom F G y φ = Sec.map φ y := rfl

section Cross
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

theorem baseS_aw (M a : ℕ) (ha : a ≤ M) (U : Scheme.{0}) (x : Sx (bidiag.obj (twX E V)) M U) :
    baseS V ((awP (twX E V) M a (M - a)).app (op U) x) = (x.sub 0 a (by omega)).map (twPi E V) := by
  unfold awP
  rw [idc_eq M a (by omega)]
  rfl

theorem ell_nat (M p q : ℕ) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk M)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk M) :
    ((twX E V).map θ.op).app (op (SimplexCategory.mk M)) ≫ ((twX E V).obj (op (SimplexCategory.mk p))).map β.op ≫
      (ℓ.app (op (SimplexCategory.mk p))).app (op (SimplexCategory.mk q)) =
    (ℓ.app (op (SimplexCategory.mk M))).app (op (SimplexCategory.mk M)) ≫ B.map β.op := by
  rw [(ℓ.app _).naturality, ← Category.assoc, ← NatTrans.comp_app, ℓ.naturality]
  simp

theorem vertS_aw (M a : ℕ) (ha : a ≤ M) (U : Scheme.{0}) (x : Sx (bidiag.obj (twX E V)) M U) :
    vertS V ℓ ((awP (twX E V) M a (M - a)).app (op U) x) =
      (x.sub a (M - a) (by omega)).map (bidiag.map ℓ ≫ (bidiagConst B).hom) := by
  unfold awP vertS
  rw [backc_eq M a (M - a) (by omega)]
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (ell_nat V ℓ M a (M - a) (idc M a)
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))) (op U)) x
  have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (ell_nat V ℓ M (M - a) (M - a)
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))) (op U)) x
  exact h1.trans h2.symm
end Cross

theorem isAW_pull_crossT : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (c : Cochain ((chains R).obj (bidiag.obj (twX E V))) K k) (hc : ∀ (M : ℕ) (s : ℤ) (h : -(M : ℤ) + k = s), c.v (-(M : ℤ)) s h = awZ R (twX E V) M ≫ (crossT V ℓ μ hk α z).v (-(M : ℤ)) s h), μ.IsAW hk ((Cochain.ofHom ((chains R).map (twPi E V))).comp α (zero_add n)) ((Cochain.ofHom ((chains R).map (bidiag.map ℓ ≫ (bidiagConst B).hom))).comp z (zero_add m)) c := by
  intro R _ E N V B ℓ I J K μ n m k hk α z c hc M w h U x
  rw [ev_def, hc M w h]
  simp only [awZ, Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp]
  change mapHom _ _ (freeGen R _ U x) (∑ a : Fin (M + 1), _) = _

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mapHom_apply', map_comp_apply', freeGen_map, evT_of_eq, evT_crossT, ev_pull, ev_pull, baseS_aw V M (a : ℕ) (by omega), vertS_aw V ℓ M (a : ℕ) (by omega)]

end GlobalTheory.PBFc.AWCross

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainProductAlexanderWhitneyFormula

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.cochain_product_alexander_whitney_formula : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (c : Cochain ((chains R).obj (bidiag.obj (twX E V))) K k) (hc : ∀ (M : ℕ) (s : ℤ) (h : -(M : ℤ) + k = s), c.v (-(M : ℤ)) s h = awZ R (twX E V) M ≫ (crossT V ℓ μ hk α z).v (-(M : ℤ)) s h), μ.IsAW hk ((Cochain.ofHom ((chains R).map (twPi E V))).comp α (zero_add n)) ((Cochain.ofHom ((chains R).map (bidiag.map ℓ ≫ (bidiagConst B).hom))).comp z (zero_add m)) c := by
  first | (exact @GlobalTheory.PBFc.AWCross.isAW_pull_crossT) | (exact GlobalTheory.PBFc.AWCross.isAW_pull_crossT) | (intros; apply GlobalTheory.PBFc.AWCross.isAW_pull_crossT  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryChartFrameGrowth

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section
namespace GlobalTheory.PBFc

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ n' (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ n x) := by
  subst hn; subst hi; rfl

theorem cast_cup (q : ℕ) {E : Spc} {n m k a b c : ℤ} (hk : n + m = k) (hc : a + b = c) (x : Ht q E n a) (y : Ht q E m b) :
    Ht.cast hk hc ((twPair q a b).cup E rfl x y) =
      (Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q a)) (res (ZMod q) (tw q b)) (res (ZMod q) (tw q k)))
        (twPair q a b) hc).cup E hk x y := by
  subst hk; subst hc; rfl

theorem cls_term (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ) (j : Fin N)
    (z : Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hz : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) z (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (a : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res _ (tw q i)) n,
      γ.1 = (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp
        (crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1) (zero_add n) ∧
      pull _ (twIso E V).hom _ n (Ht.cast (by ring) (by ring) (cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (CohomologyClass.mk a))
        (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) : Ht q _ n i) = CohomologyClass.mk γ := by
  set c := (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp
    (crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1) (zero_add n) with hcdef
  have hAW := GlobalTheory.T.cochain_product_alexander_whitney_formula V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1 c (fun M s h => by
    rw [hcdef, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, awChains_f])
  have hδ := aw_cocycle (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _)
    (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (twPi E V))) a (zero_add _))
    (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) z (zero_add _)) c (by
      simpa only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe] using hAW)
  refine ⟨Cocycle.mk c (n + 1) rfl hδ, rfl, ?_⟩
  rw [pull_cast]
  change Ht.cast _ _ (cpull ((chains (ZMod q)).map (twIso E V).hom) _ _ ((twPair q _ _).cup _ rfl _ _)) = _
  rw [Pair.cup_pull, cast_cup]
  change (twPairI q i ((j : ℕ) : ℤ)).cup _ _ (pull _ (twIso E V).hom _ _ (pull _ (pullback.fst V (PGL.pr N)) _ _ (CohomologyClass.mk a)))
    (pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) = _
  rw [← pull_comp, twIso_hom_fst, ← hz]
  refine Pair.cup_spec _ _ _ (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (twPi E V))) a (zero_add _)) _ _ ?_
  simpa only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe] using hAW

theorem pbfMap_eq_cpull_aw (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ)
    (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hz : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n)
    (hb : b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1)) :
    pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) =
      cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n (CohomologyClass.mk b) := by
  choose γ hγ hγc using fun j : Fin N => cls_term q V ℓ n i j (z j) (hz j) (a j)
  have e1 : pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) =
      ∑ j : Fin N, CohomologyClass.mk (γ j) := by
    unfold pbfMap

    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hγc j
  have e2 : zcomp (Cocycle.ofHom (awChains (ZMod q) (twX E V))) b (zero_add n) = ∑ j : Fin N, γ j := by
    apply Cocycle.ext
    have hs := map_sum (AddSubgroup.subtype (cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res (ZMod q) (tw q i)) n)) γ Finset.univ
    refine Eq.trans ?_ hs.symm
    change _ = ∑ j, (γ j).1
    simp only [hγ]
    change (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp b.1 (zero_add n) = _
    rw [hb, phi_apply]
    exact map_sum (AddMonoidHom.mk' (fun x : Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n =>
      (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp x (zero_add n)) (fun x y => Cochain.comp_add _ _ _ _)) _ _
  rw [e1, cpre_mk, e2]
  exact (map_sum (AddMonoidHom.mk' (CohomologyClass.mk : Cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res _ (tw q i)) n → _)
    (fun x y => CohomologyClass.mk_add x y)) _ _).symm

end GlobalTheory.PBFc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCocycleClassesPullbackCup

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.twisted_cocycle_classes_pullback_cup : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) = pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n) (hb : b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1)), pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) = cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n (CohomologyClass.mk b) := by
  first | (exact @GlobalTheory.PBFc.pbfMap_eq_cpull_aw) | (exact GlobalTheory.PBFc.pbfMap_eq_cpull_aw) | (intros; apply GlobalTheory.PBFc.pbfMap_eq_cpull_aw  <;> assumption)
end
end
