module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeMulVecLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossProductTwistedLeibnizRuleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCocycleClassesPullbackCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameFunctionCompare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullAwChainsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GagaLineGeneratorComplex

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFc

theorem crossT_ι_eq_zero_of_vanish {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ}
    (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (p : ℤ)
    (hα : ∀ c r hr, p < c → α.v c r hr = 0) (c l t : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + k = r)
    (hc : p < c) :
    (biChains R (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (crossT V ℓ μ hk α z).v t r hr = 0 := by
  have ht : c + l = t := h
  by_cases hcl : c ≤ 0 ∧ l ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
    obtain rfl : t = -((a + b : ℕ) : ℤ) := by push_cast; omega
    rw [← cancel_epi (biChainsXIso R (twX E V) a b).inv, comp_zero]
    refine free_ext _ _ fun U y => ?_
    have e1 := evT_crossT V ℓ μ hk α z a b r hr U y
    unfold evT at e1
    refine e1.trans ?_
    have h0 : ev α a _ rfl U (baseS V y) = 0 := by
      rw [ev_def, hα _ _ _ hc, comp_zero]
      exact map_zero (mapHom _ _ (freeGen R _ U (baseS V y)))
    rw [h0, map_zero, LinearMap.zero_apply, smul_zero]
    exact (map_zero (mapHom _ _ (freeGen R _ U y))).symm
  · exact (biChains_isZero (R := R) (twX E V) c l (by omega)).eq_of_src _ _

end GlobalTheory.PBFc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainProductVanishingAboveDegree

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.cochain_product_vanishing_above_degree : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (p : ℤ) (hα : ∀ c r hr, p < c → α.v c r hr = 0) (c l t : ℤ) (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + k = r) (hc : p < c), (biChains R (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (crossT V ℓ μ hk α z).v t r hr = 0 := by
  first | (exact @GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish) | (exact GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish) | (intros; apply GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCocycleSimplicialLevelsCup

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.twisted_cocycle_simplicial_levels_cup : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ (a : ℕ) (j : Fin N), CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ)) (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀), ∀ p ≤ (0 : ℤ), ∃ ψ : ∀ m, (∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) → CohomologyClass ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m, (∀ m, Function.Bijective (ψ m)) ∧ ∀ n m, n + p = m → ∀ α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)), (∀ j c r hr, p < c → (α j).v c r hr = 0) → ∀ (a : ∀ j : Fin N, Cocycle (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (b : Cocycle ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m), (∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X p) ≫ (a j).1.v 0 r hr = (α j).v p r hr') → (∀ (k t : ℤ) (h : p + k = t) r hr hr', b.1.v k r hr = (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) p k t h ≫ (phi q V ℓ i (fun j => (z j).1) n α).v t r hr') → ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
  first | (exact @GlobalTheory.PBFg.graded_bijective) | (exact GlobalTheory.PBFg.graded_bijective) | (intros; apply GlobalTheory.PBFg.graded_bijective  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsIsStrictlyLE

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFc
open GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ

instance res_isStrictlyGE (R : Type) [CommRing R] (F : Shv R) : (res R F).IsStrictlyGE 0 := by
  unfold res; infer_instance

instance chains_isStrictlyLE (R : Type) [CommRing R] (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

variable (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
  (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)

theorem phi_δ (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n m : ℤ) (hnm : n + 1 = m)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    phi q V ℓ i (fun j => (z j).1) m (fun j => δ (n - 2 * ((j : ℕ) : ℤ)) (m - 2 * ((j : ℕ) : ℤ)) (α j)) =
      δ n m (phi q V ℓ i (fun j => (z j).1) n α) := by
  have hs : ∀ (f : Fin N → Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n),
      δ n m (∑ j, f j) = ∑ j, δ n m (f j) := fun f => map_sum (AddMonoidHom.mk' (δ n m) (δ_add n m)) f _
  rw [phi_apply, phi_apply, hs]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = δ n m _
  rw [GlobalTheory.T.crossProductTwisted_leibniz_rule V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _)
    (show n - 2 * ((j : ℕ) : ℤ) + 1 = m - 2 * ((j : ℕ) : ℤ) by omega) rfl hnm (by omega) (by omega),
    Cocycle.δ_eq_zero (z j), crossT_zero_right, smul_zero, add_zero]

theorem phi_van (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (p n : ℤ)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (hα : ∀ j c r hr, p < c → (α j).v c r hr = 0) (c l t : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + n = r) (hc : p < c) :
    (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (phi q V ℓ i z n α).v t r hr = 0 := by
  let ev₀ : Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n →+ _ :=
    AddMonoidHom.mk' (fun γ => (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ γ.v t r hr)
      (fun γ γ' => by rw [Cochain.add_v, Preadditive.comp_add])
  change ev₀ _ = 0

  rw [phi_apply, map_sum]
  exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.cochain_product_vanishing_above_degree V ℓ _ _ (α j) (z j) p (hα j) c l t h r hr hc

theorem pull_iso_bijective {E E' : Spc} (e : E ≅ E') (F : Shv (ZMod q)) (n : ℤ) :
    Function.Bijective (pull (ZMod q) e.hom F n) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨pull (ZMod q) e.inv F n y, ?_⟩⟩
  · have hx := (pull_comp (ZMod q) e.inv e.hom F n x).symm
    have hy := (pull_comp (ZMod q) e.inv e.hom F n y).symm
    rw [e.inv_hom_id, pull_id] at hx hy
    exact hx.symm.trans ((congrArg _ hxy).trans hy)
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem pbf_of_model [NeZero q] (hE : Inv q E)
    (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hzd : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map
        (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (hzc : ∀ (a : ℕ) (j : Fin N),
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j)
        (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ))
    (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀) : PBF q V := by
  intro n i
  have hf1 := pull_iso_bijective q (twIso E V) (tw q i) n
  have hf2 := pull_awChains_bijective (ZMod q) (twX E V) (res _ (tw q i)) n
  let φ : (∀ j : Fin N, CohomologyClass ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (n - 2 * ((j : ℕ) : ℤ))) → CohomologyClass (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n :=
    fun x => Function.surjInv hf2.2 (pull _ (twIso E V).hom _ n (pbfMap q V n i x))
  have hφ : ∀ (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (n - 2 * ((j : ℕ) : ℤ))) (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n),
      b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1) →
      φ (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
    intro a b hb
    apply hf2.1
    rw [Function.surjInv_eq hf2.2]
    exact GlobalTheory.T.twisted_cocycle_classes_pullback_cup q V ℓ n i z hzd a b hb
  have hb : Function.Bijective φ :=
    GlobalTheory.ColFilt.bijective_total_of_terms (ZMod q) (biChains (ZMod q) (twX E V))
      (fun p k h => biChains_isZero (twX E V) p k h) ((chains (ZMod q)).obj E)
      (fun j : Fin N => res _ (tw q (i - ((j : ℕ) : ℤ)))) (res _ (tw q i)) (fun j : Fin N => 2 * ((j : ℕ) : ℤ))
      (phi q V ℓ i (fun j => (z j).1)) (fun n m h α => phi_δ q V ℓ i z n m h α)
      (fun p n α hα => phi_van q V ℓ i (fun j => (z j).1) p n α hα)
      (GlobalTheory.T.twisted_cocycle_simplicial_levels_cup q V hE ℓ i z hzc hD) n φ hφ
  have hcomp : (pull _ (twIso E V).hom _ n) ∘ pbfMap q V n i = (cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n) ∘ φ :=
    funext fun x => (Function.surjInv_eq hf2.2 _).symm
  exact (Function.Bijective.of_comp_iff' hf1 _).1 (hcomp ▸ hf2.comp hb)

end GlobalTheory.PBFc

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfDiscreteSpaces

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFg
open GlobalTheory.EtC

def invPSh (q : ℕ) : PSh where
  obj U := PLift (IsUnit (q : Scheme.Γ.obj U))
  map f := TypeCat.ofHom fun h => ⟨(map_natCast (Scheme.Γ.map f).hom q) ▸ h.down.map (Scheme.Γ.map f).hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev lineSp (q : ℕ) : Spc := ptimes (invPSh q) (ofCat (glCat 1))

abbrev lineSp.line (q : ℕ) : lineSp q ⟶ ofCat (glCat 1) := ptimes.snd _ _

theorem inv_lineSp (q : ℕ) : Inv q (lineSp q) := fun _ ⟨y⟩ => y.1.down

theorem inv_of_map {E E' : Spc} (f : E ⟶ E') {q : ℕ} (h : Inv q E') : Inv q E := fun U ⟨x⟩ =>
  h U ⟨((f.app (op (SimplexCategory.mk 0))).app (op U)) x⟩

theorem isUnit_of_simplex {q : ℕ} {E : Spc} (hE : Inv q E) (p : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ)
    (x : (E.obj p).obj U) : IsUnit (q : Scheme.Γ.obj U) :=
  hE U.unop ⟨(E.map (SimplexCategory.const (SimplexCategory.mk 0) p.unop 0).op).app U x⟩

variable (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E)

def colInv (p : SimplexCategoryᵒᵖ) : ptimes (E.obj p) (Fib N) ⟶ disc.obj (invPSh q) where
  app n := { app := fun U => TypeCat.ofHom (fun y => ⟨isUnit_of_simplex hE p U y.1⟩), naturality := fun _ _ _ => rfl }
  naturality _ _ _ := rfl

def colLine (p : SimplexCategoryᵒᵖ) : ptimes (E.obj p) (Fib N) ⟶ lineSp q :=
  (ptimesIsLimit _ _).lift (BinaryFan.mk (colInv q hE p) (ptimes.snd _ _ ≫ Fib.line N))

theorem colLine_line (p : SimplexCategoryᵒᵖ) : colLine q hE p ≫ lineSp.line q = ptimes.snd (E.obj p) (Fib N) ≫ Fib.line N :=
  (ptimesIsLimit _ _).fac _ ⟨WalkingPair.right⟩

def ellB : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (lineSp q) where
  app p := colLine q hE p
  naturality _ _ _ := rfl

theorem pull_cast {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E₂ n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f (tw q i) n x : Ht q E₁ n i) := by
  subst hn hi; rfl

theorem pull_cpow [NeZero q] {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) (h : Inv q E₂) (x : Ht q E₂ 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (a6nat_holds q).2.1 f h]
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (a6nat_holds q).1, ih]

theorem mk_zcomp_ofHom {R : Type} [CommRing R] {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) {F : Shv R} {n : ℤ}
    (z : Cocycle ((chains R).obj E₂) (res R F) n) :
    CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _)) = pull R f F n (CohomologyClass.mk z) :=
  rfl

theorem diag_line : (bidiag.map (ellB q V hE) ≫ (bidiagConst (lineSp q)).hom) ≫ lineSp.line q =
    bidiag.map (twLine E V) ≫ (bidiagConst _).hom := rfl

theorem pbf_of_disc : ∀ (q : ℕ) [NeZero q] (N : ℕ),
    (∀ (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V) →
      ∀ {E : Spc} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V := by
  intro q _ N hD E V hE
  have hB := inv_lineSp q
  have hP : Inv q (pullback V (PGL.pr N)) := inv_of_map (pullback.fst V (PGL.pr N)) hE
  choose z hz using fun j : Fin N => CohomologyClass.mk_surjective (cpow q (c1 q (lineSp.line q)) (j : ℕ))
  refine GlobalTheory.PBFc.pbf_of_model q V (ellB q V hE) hE z (fun j => ?_) (fun a j => ?_) hD
  · rw [mk_zcomp_ofHom, hz, pull_cpow q _ hB, (a6nat_holds q).2.2.1 _ _ hB, pull_cpow q _ hP,
      (a6nat_holds q).2.2.1 _ _ hP, twIso_line, diag_line]
  · rw [mk_zcomp_ofHom, hz, pull_cpow q _ hB, (a6nat_holds q).2.2.1 _ _ hB]
    exact congrArg (fun L => cpow q (c1 q L) (j : ℕ)) (colLine_line q hE _)

end GlobalTheory.PBFg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfDiscreteSpacesStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.projectiveBundleFormula_of_discrete_spaces : ∀ (q : ℕ) [NeZero q] (N : ℕ), (∀ (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V) → ∀ {E : Spc} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V := by
  first | (exact @GlobalTheory.PBFg.pbf_of_disc) | (exact GlobalTheory.PBFg.pbf_of_disc) | (intros; apply GlobalTheory.PBFg.pbf_of_disc  <;> assumption)
end
end
