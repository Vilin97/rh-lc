module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoveringOfForallMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueIsTransfer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeHomExtOfCovering
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitByBaseChange
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueIsTransfer
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodSemilinear
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceOfFiniteEtaleDegree

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TrDeg

open GlobalTheory.EtC.Tr

variable (R : Type) [CommRing R]

theorem chainMap_comp {X Y Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Y) (t' : freeSch R Y ⟶ freeSch R Z) :
    chainMap R (t ≫ t') = chainMap R t ≫ chainMap R t' := by
  have : simpMap R (t ≫ t') = simpMap R t ≫ simpMap R t' := by ext; rfl
  rw [chainMap, this, Functor.map_comp]
  exact CategoryTheory.Functor.map_comp _ _ _

theorem chainMap_add {X Y : Scheme.{0}} (t t' : freeSch R X ⟶ freeSch R Y) :
    chainMap R (t + t') = chainMap R t + chainMap R t' := by
  have : simpMap R (t + t') = simpMap R t + simpMap R t' := by ext; rfl
  rw [chainMap, this, (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map_add]
  exact (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map_add

theorem along_comp {X Y Z : Scheme.{0}} (F : Shv R) (n : ℤ) (t : freeSch R X ⟶ freeSch R Y) (t' : freeSch R Y ⟶ freeSch R Z)
    (x : H R (sch.obj Z) F n) : along R F n (t ≫ t') x = along R F n t (along R F n t' x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, chainMap_comp, Cochain.ofHom_comp]

theorem along_add {X Y : Scheme.{0}} (F : Shv R) (n : ℤ) (t t' : freeSch R X ⟶ freeSch R Y)
    (x : H R (sch.obj Y) F n) : along R F n (t + t') x = along R F n t x + along R F n t' x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine (congrArg CohomologyClass.mk (Cocycle.ext ?_)).trans (CohomologyClass.mk_add _ _)
  simp [zcomp, chainMap_add, Cochain.ofHom_add, Cochain.add_comp]

theorem along_nsmul_id (X : Scheme.{0}) (F : Shv R) (n : ℤ) (d : ℕ) (x : H R (sch.obj X) F n) :
    along R F n (d • 𝟙 (freeSch R X)) x = d • x := by
  induction d with
  | zero =>
    have h := along_add R F n (0 : freeSch R X ⟶ freeSch R X) 0 x
    rw [add_zero] at h
    rw [zero_smul, zero_smul]
    exact left_eq_add.1 h
  | succ d ih => rw [succ_nsmul, succ_nsmul, along_add, ih, along_id]

theorem generate_singleton_mem {U X : Scheme.{0}} (u : U ⟶ X) [Etale u] [Surjective u] :
    Sieve.generate (Presieve.singleton u) ∈ Scheme.etaleTopology X :=
  Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff (P := @Etale) u).2 ⟨(inferInstance : Surjective u).surj, inferInstance⟩)

theorem transfer_comp {Y X U : Scheme.{0}} {f : Y ⟶ X} {u : U ⟶ X} [Etale u] [Surjective u] {d : ℕ}
    {s : Fin d → (U ⟶ Y)} (hs : SplitBy f u s) {t : freeSch R X ⟶ freeSch R Y} (ht : IsTransfer R f t) :
    t ≫ (free R).map (yoneda.map f) = d • 𝟙 _ := by
  refine free_hom_ext_of_covering R _ _ _ _ (generate_singleton_mem u) ?_
  rintro V v ⟨_, g, _, ⟨⟩, rfl⟩
  have hg := splitBy_baseChange hs g
  rw [← Category.assoc, ht.apply_of_splitBy R hg, Preadditive.sum_comp]
  have h1 : ∀ j, (free R).map (yoneda.map (g ≫ s j)) ≫ (free R).map (yoneda.map f) =
      (free R).map (yoneda.map (g ≫ u)) := fun j => by
    rw [← Functor.map_comp, ← Functor.map_comp, hg.1 j]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Preadditive.comp_nsmul, Category.comp_id]

theorem trH_pull {Y X U : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] {u : U ⟶ X} [Etale u] [Surjective u] {d : ℕ}
    {s : Fin d → (U ⟶ Y)} (hs : SplitBy f u s) (F : Shv R) (n : ℤ) (x : H R (sch.obj X) F n) :
    trH R f F n (pull R (sch.map f) F n x) = d • x := by
  rw [trH, ← along_free, ← along_comp,
    transfer_comp R hs (transfer_spec R (existsUnique_isTransfer R f).exists), along_nsmul_id]

end GlobalTheory.EtC.TrDeg

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RedCompatOfFiniteEtale

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.Tr

open GlobalTheory.EtC.CupSpec

section CyclicComplexMaps

variable {R : Type} [CommRing R]

theorem chainMap_f {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) (p : ℕ) :
    (chainsXIso R (sch.obj X) p).inv ≫ (chainMap R t).f (-(p : ℤ)) = t ≫ (chainsXIso R (sch.obj Z) p).inv := by
  have h1 : (chainMap R t).f (-(p : ℤ)) =
      (chainsXIso R (sch.obj X) p).hom ≫ ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simpMap R t)).f p ≫
        (chainsXIso R (sch.obj Z) p).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl
  rw [h1, Iso.inv_hom_id_assoc]
  rfl

theorem ev_chainMap {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) {I : Cx R} {n : ℤ}
    (α : Cochain ((chains R).obj (sch.obj Z)) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (y : Sx (sch.obj X) p U) :
    ev ((Cochain.ofHom (chainMap R t)).comp α (zero_add n)) p s h U y =
      Sec.map ((chainsXIso R (sch.obj Z) p).inv ≫ α.v _ _ h) (Sec.map t (freeGen R (yoneda.obj X) U y)) := by
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainMap_f]
  rfl

end CyclicComplexMaps

section Key

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem secMap_sum {F G : Shv R} {ι : Type*} (s : Finset ι) (g : ι → (F ⟶ G)) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (∑ j ∈ s, g j) a = ∑ j ∈ s, Sec.map (g j) a :=
  map_sum (mapHom F G a) g s

theorem exists_free_restr (P : PSh) : ∃ ι : (free R).obj P ⟶ (restr φ).obj ((free S).obj P),
    ∀ U x, Sec.map ι (freeGen R P U x) = (show Sec ((restr φ).obj ((free S).obj P)) U from freeGen S P U x) :=
  free_exists P _ (fun U x => show Sec ((restr φ).obj ((free S).obj P)) U from freeGen S P U x)
    (fun V U g x => freeGen_res P g x)

theorem isTransfer_reduce {Z X : Scheme.{0}} {f : Z ⟶ X} {t : freeSch R X ⟶ freeSch R Z} (ht : IsTransfer R f t)
    (ι : freeSch R Z ⟶ (restr φ).obj (freeSch S Z))
    (hι : ∀ U x, Sec.map ι (freeGen R (yoneda.obj Z) U x) =
      (show Sec ((restr φ).obj (freeSch S Z)) U from freeGen S (yoneda.obj Z) U x))
    (t' : freeSch S X ⟶ freeSch S Z)
    (ht' : ∀ U x, Sec.map t' (freeGen S (yoneda.obj X) U x) =
      (show Sec (freeSch S Z) U from Sec.map ι (Sec.map t (freeGen R (yoneda.obj X) U x)))) :
    IsTransfer S f t' := by
  intro T x m s hs hiso
  apply free_ext
  intro V w
  have e := congrArg (fun g => Sec.map ι (Sec.map g (freeGen R (yoneda.obj T) V w))) (ht T x m s hs hiso)
  change Sec.map ι (Sec.map t (Sec.map ((free R).map (yoneda.map x)) (freeGen R (yoneda.obj T) V w))) =
    Sec.map ι (Sec.map (∑ j, (free R).map (yoneda.map (s j))) (freeGen R (yoneda.obj T) V w)) at e
  change Sec.map t' (Sec.map ((free S).map (yoneda.map x)) (freeGen S (yoneda.obj T) V w)) =
    Sec.map (∑ j, (free S).map (yoneda.map (s j))) (freeGen S (yoneda.obj T) V w)
  rw [freeGen_map, ht']
  rw [freeGen_map] at e
  refine e.trans ?_
  rw [secMap_sum, secMap_sum]
  refine (map_sum (ι.hom.app (op V)).hom _ Finset.univ).trans (Finset.sum_congr rfl fun j _ => ?_)
  change Sec.map ι (Sec.map ((free R).map (yoneda.map (s j))) (freeGen R (yoneda.obj T) V w)) = _
  rw [freeGen_map, freeGen_map, hι]

theorem key_free {Z X : Scheme.{0}} {f : Z ⟶ X} {I : Shv R} {J : Shv S} (A : freeSch R Z ⟶ I) (B : freeSch S Z ⟶ J)
    (ρ' : I ⟶ (restr φ).obj J)
    (hAB : ∀ V z, Sec.map B (freeGen S (yoneda.obj Z) V z) = Sec.map ρ' (Sec.map A (freeGen R (yoneda.obj Z) V z)))
    {tR : freeSch R X ⟶ freeSch R Z} (htR : IsTransfer R f tR) {tS : freeSch S X ⟶ freeSch S Z}
    (huniq : ∀ t, IsTransfer S f t → t = tS) (U : Scheme.{0}) (y : U ⟶ X) :
    Sec.map B (Sec.map tS (freeGen S (yoneda.obj X) U y)) =
      Sec.map ρ' (Sec.map A (Sec.map tR (freeGen R (yoneda.obj X) U y))) := by
  obtain ⟨ι, hι⟩ := exists_free_restr φ (yoneda.obj Z)
  obtain ⟨t', ht'⟩ := free_exists (R := S) (yoneda.obj X) (freeSch S Z)
    (fun U y => show Sec (freeSch S Z) U from Sec.map ι (Sec.map tR (freeGen R (yoneda.obj X) U y)))
    (fun V U g y => by
      refine (map_res ι g _).trans ?_
      change Sec.map ι (Sec.res g (Sec.map tR (freeGen R (yoneda.obj X) U y))) = _
      rw [map_res, freeGen_res])
  have hT := huniq t' (isTransfer_reduce φ htR ι hι t' ht')
  subst hT
  rw [ht']
  have hm : ι ≫ (restr φ).map B = A ≫ ρ' := free_ext _ _ (fun V z => by
    change Sec.map B (Sec.map ι (freeGen R (yoneda.obj Z) V z)) = Sec.map ρ' (Sec.map A (freeGen R (yoneda.obj Z) V z))
    rw [hι]
    exact hAB V z)
  exact congrArg (fun g => Sec.map g (Sec.map tR (freeGen R (yoneda.obj X) U y))) hm

end Key

theorem redCompat_of_finite_etale (l : ℕ) [Fact l.Prime] {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f]
    (hex : ∀ (R : Type) [CommRing R], ∃! t, IsTransfer R f t) (n i : ℤ) : RedCompat l f n i := by
  intro k x
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl⟩
  have hd : l ^ k ∣ l ^ (k + 1) := pow_dvd_pow l (Nat.le_succ k)
  obtain ⟨t0, ht0, -⟩ := hex (ZMod (l ^ (k + 1)))
  have htQ := transfer_spec (ZMod (l ^ (k + 1))) ⟨t0, ht0⟩
  obtain ⟨t1, ht1, hu1⟩ := hex (ZMod (l ^ k))
  have huniq : ∀ t, IsTransfer (ZMod (l ^ k)) f t → t = transfer (ZMod (l ^ k)) f := fun t ht =>
    (hu1 t ht).trans (hu1 _ (transfer_spec _ ⟨t1, ht1⟩)).symm
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (redMap (l ^ (k + 1)) (l ^ k) i).image_exists (sch.obj Z) n α
  have h1 : red (l ^ (k + 1)) (l ^ k) (sch.obj Z) n i (CohomologyClass.mk α) = CohomologyClass.mk β :=
    (redMap (l ^ (k + 1)) (l ^ k) i).op_spec _ n α β hβ
  rw [h1]
  have key := (redMap (l ^ (k + 1)) (l ^ k) i).op_spec (sch.obj X) n
    (zcomp (Cocycle.ofHom (chainMap _ (transfer _ f))) α (zero_add n))
    (zcomp (Cocycle.ofHom (chainMap _ (transfer _ f))) β (zero_add n)) (by
      intro p s h U y
      change ev ((Cochain.ofHom (chainMap _ (transfer _ f))).comp β.1 (zero_add n)) p s h U y =
        (redMap (l ^ (k + 1)) (l ^ k) i).app U s
          (ev ((Cochain.ofHom (chainMap _ (transfer _ f))).comp α.1 (zero_add n)) p s h U y)
      rw [ev_chainMap, ev_chainMap]
      exact key_free (ZMod.castHom hd (ZMod (l ^ k))) _ _
        (ScalarExt.semiHom (redMap (l ^ (k + 1)) (l ^ k) i) (ScalarExt.zmod_semilinear hd _) s)
        (fun V z => (ev_def β.1 p s h V z).symm.trans ((hβ p s h V z).trans (congrArg _ (ev_def α.1 p s h V z))))
        htQ huniq U y)
  exact key

end GlobalTheory.EtC.Tr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFiniteEtaleGaloisCoverLadic

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TrGal

open GlobalTheory.EtC.Tr GlobalTheory.EtC.TrDeg

variable (R : Type) [CommRing R]

theorem splitBy_of_equiv {Y X V : Scheme.{0}} (f : Y ⟶ X) (y : V ⟶ X) {G : Type} {m : ℕ} (e : Fin m ≃ G)
    (a : G → (V ⟶ Y)) (ha : ∀ g, a g ≫ f = y)
    (h : IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 V) (by rw [ha g, Category.id_comp])) :
      ∐ (fun _ : G => V) ⟶ pullback f y)) : SplitBy f y (fun j => a (e j)) := by
  refine ⟨fun j => ha _, ?_⟩
  let w : ∐ (fun _ : Fin m => V) ≅ ∐ (fun _ : G => V) := Sigma.reindex e (fun _ : G => V)
  have hw : ∀ j, Sigma.ι (fun _ : Fin m => V) j ≫ w.hom = Sigma.ι (fun _ : G => V) (e j) := fun j =>
    Sigma.ι_reindex_hom e (fun _ : G => V) j
  convert (inferInstance : IsIso (w.hom ≫ (Sigma.desc (fun g => pullback.lift (a g) (𝟙 V) (by rw [ha g, Category.id_comp])) :
      ∐ (fun _ : G => V) ⟶ pullback f y)))
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_desc, reassoc_of% (hw j), Sigma.ι_desc]

theorem along_sum {X Y : Scheme.{0}} (F : Shv R) (n : ℤ) {ι : Type} (s : Finset ι) (t : ι → (freeSch R X ⟶ freeSch R Y))
    (x : H R (sch.obj Y) F n) : along R F n (∑ j ∈ s, t j) x = ∑ j ∈ s, along R F n (t j) x :=
  map_sum (AddMonoidHom.mk' (fun u : freeSch R X ⟶ freeSch R Y => along R F n u x) (fun u v => along_add R F n u v x)) t s

theorem pull_trH {Y X V : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Y)} (hs : SplitBy f y s) (F : Shv R) (n : ℤ) (x : H R (sch.obj Y) F n) :
    pull R (sch.map y) F n (trH R f F n x) = ∑ j, pull R (sch.map (s j)) F n x := by
  rw [trH, ← along_free, ← along_comp,
    (transfer_spec R (existsUnique_isTransfer R f).exists).apply_of_splitBy R hs, along_sum]
  simp only [along_free]

theorem exists_trace_galois : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, ∃ tr : Hl l (sch.obj Y) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i,
  (∀ x, tr (pullHl l (sch.map f) n i x) = Fintype.card G • x) ∧ ∀ y, pullHl l (sch.map f) n i (tr y) = ∑ g, pullHl l (sch.map (a g)) n i y := by
  intro l _ Y X f _ _ _ G _ a ha hiso n i
  have hs := splitBy_of_equiv f f (Fintype.equivFin G).symm a ha hiso
  have h := trHl_spec l (redCompat_of_finite_etale l f (fun R _ => existsUnique_isTransfer R f) n i)
  refine ⟨trHl l f n i, fun x => Subtype.ext (funext fun k => ?_), fun y => Subtype.ext (funext fun k => ?_)⟩
  · exact (h _ k).trans (trH_pull (ZMod (l ^ k)) f hs (tw (l ^ k) i) n (x.1 k))
  · rw [← Equiv.sum_comp (Fintype.equivFin G).symm, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    exact (congrArg (pull (ZMod (l ^ k)) (sch.map f) (tw (l ^ k) i) n) (h y k)).trans
      (pull_trH (ZMod (l ^ k)) f hs (tw (l ^ k) i) n (y.1 k))

end GlobalTheory.EtC.TrGal

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFiniteEtaleGaloisCoverLadicStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_trace_finiteEtaleGaloisCover_ladic : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, ∃ tr : Hl l (sch.obj Y) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i,
  (∀ x, tr (pullHl l (sch.map f) n i x) = Fintype.card G • x) ∧ ∀ y, pullHl l (sch.map f) n i (tr y) = ∑ g, pullHl l (sch.map (a g)) n i y := by
  first | (exact @GlobalTheory.EtC.TrGal.exists_trace_galois) | (exact GlobalTheory.EtC.TrGal.exists_trace_galois) | (intros; apply GlobalTheory.EtC.TrGal.exists_trace_galois  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLAdicRationalCohomologyGaloisCoverInvari

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem pullHQ_galoisCover_inv : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, Function.Injective (pullHQ l (sch.map f) n i) ∧
  LinearMap.range (pullHQ l (sch.map f) n i) = ⨅ g, LinearMap.ker (pullHQ l (sch.map (a g)) n i - LinearMap.id) := by
  intro l _ Y X f _ _ _ G _ a ha hiso n i
  obtain ⟨tr, h1, h2⟩ := GlobalTheory.T.exists_trace_finiteEtaleGaloisCover_ladic l f G a ha hiso n i
  set F := pullHQ l (sch.map f) n i with hF
  set T := tr.baseChange ℚ_[l] with hT
  have pqc : ∀ {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C),
      pullHQ l (sch.map (u ≫ v)) n i = (pullHQ l (sch.map u) n i).comp (pullHQ l (sch.map v) n i) := by
    intro A B C u v
    rw [pullHQ, pullHQ, pullHQ, ← LinearMap.baseChange_comp, ← pullHl_comp, ← Functor.map_comp]
  have pqi : ∀ A : Scheme.{0}, pullHQ l (sch.map (𝟙 A)) n i = LinearMap.id := by
    intro A
    rw [pullHQ, CategoryTheory.Functor.map_id, pullHl_id, LinearMap.baseChange_id]
  have key1 : ∀ x, T (F x) = (Fintype.card G : ℚ_[l]) • x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hF, pullHQ, hT, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, h1, Nat.cast_smul_eq_nsmul]
      exact TensorProduct.tmul_smul _ _ _
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
  have key2 : ∀ y, F (T y) = ∑ g, pullHQ l (sch.map (a g)) n i y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hF, pullHQ, hT, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, h2, TensorProduct.tmul_sum]
      simp only [pullHQ, LinearMap.baseChange_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, ← Finset.sum_add_distrib]; simp only [map_add (f := _)]
  have comp : ∀ g, (pullHQ l (sch.map (a g)) n i).comp F = F := by
    intro g
    rw [hF, ← pqc, ha g]
  by_cases hG : Fintype.card G = 0
  ·
    haveI : IsEmpty G := Fintype.card_eq_zero_iff.mp hG
    have hS : IsEmpty ↥(∐ (fun _ : G => Y)) := by
      constructor
      intro p
      obtain ⟨j, _⟩ := (sigmaOpenCover (fun _ : G => Y)).exists_eq p
      exact isEmptyElim (show G from j)
    haveI hYe : IsEmpty Y :=
      ⟨fun y => hS.false ((pullback.lift (𝟙 Y) (𝟙 Y) rfl ≫ inv (Sigma.desc (fun g =>
        pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f)).base y)⟩
    haveI : IsEmpty X := ⟨fun x => by
      obtain ⟨y, _⟩ := (inferInstance : Surjective f).surj x
      exact hYe.false y⟩
    haveI : IsIso f := isIso_of_isEmpty f
    have e1 : (pullHQ l (sch.map (inv f)) n i).comp F = LinearMap.id := by
      rw [hF, ← pqc, IsIso.inv_hom_id, pqi]
    have e2 : F.comp (pullHQ l (sch.map (inv f)) n i) = LinearMap.id := by
      rw [hF, ← pqc, IsIso.hom_inv_id, pqi]
    refine ⟨fun x y hxy => ?_, ?_⟩
    · have := congrArg (pullHQ l (sch.map (inv f)) n i) hxy
      rwa [← LinearMap.comp_apply, e1, ← LinearMap.comp_apply, e1] at this
    · rw [iInf_of_empty, LinearMap.range_eq_top]
      intro y
      exact ⟨pullHQ l (sch.map (inv f)) n i y, by rw [← LinearMap.comp_apply, e2, LinearMap.id_apply]⟩
  have hc : (Fintype.card G : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hG
  refine ⟨fun x y hxy => ?_, ?_⟩
  · have := congrArg T hxy
    rw [key1, key1] at this
    exact smul_right_injective _ hc this
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
      intro g
      rw [← LinearMap.comp_apply, comp g, sub_self]
    · intro y hy
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy
      refine ⟨(Fintype.card G : ℚ_[l])⁻¹ • T y, ?_⟩
      rw [map_smul, key2]
      simp only [hy, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hc, one_smul]

end GlobalTheory
end
end
