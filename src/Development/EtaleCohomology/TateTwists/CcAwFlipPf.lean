module

public import Development.EtaleCohomology.TateTwists.CcCupFlipPf
public import Development.EtaleCohomology.TateTwists.CupflipHomotopyPf
public import Development.EtaleCohomology.TateTwists.EtaleSimplicialChainsFreeDescription
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
import Mathlib.Tactic.Lemma
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
public import Development.EtaleCohomology.TateTwists.EtaleCochainExistsOfNaturalEvaluation
public import Development.EtaleCohomology.TateTwists.EtaleChainCochainExistsOfEvalData
public import Development.EtaleCohomology.TateTwists.EtaleFreeSheafUniversalProperty
public import Development.EtaleCohomology.TateTwists.EtaleFreeSheafHomUniversalPropertyHolds

-- Source module: Development.EtaleCohomology.TateTwists.EtaleSimplicialChainsBasicPropertiesHold

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ChainsBasicPf

variable (R : Type) [CommRing R]

lemma chainsN_d (E : Spc) (p : ℕ) :
    ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ p

lemma chains_map_f {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    ((chains R).map f).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv :=
  HomologicalComplex.extendMap_f _ _ rfl

lemma chains_d (E : Spc) (p : ℕ) :
    ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ ((chainsN R).obj E).d (p + 1) p ≫ (chainsXIso R E p).inv :=
  HomologicalComplex.extend_d_eq _ _ rfl rfl

lemma chains_d' (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom =
      ((chainsN R).obj E).d (p + 1) p := by
  rw [chains_d R E p]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma chains_le (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

end LateralTheory.EtaleFoundations.ChainsBasicPf

open LateralTheory.EtaleFoundations.ChainsBasicPf in
theorem LateralTheory.EtaleFoundations.etale_simplicial_chains_basic_properties_hold : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := by
  intro R _
  refine ⟨fun E => chains_le R E, fun {E E'} f p => ?_, fun E p => ?_⟩
  · rw [chains_map_f R f p]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [chains_d' R E p]
    exact chainsN_d R E p
end
end

-- Source module: Development.EtaleCohomology.TateTwists.EtaleCochainComplexBasicPropertiesOfComponents

section

@[expose] public section

namespace LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
theorem etale_cochain_complex_basic_properties_of_components : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := by
  apply LateralTheory.EtaleFoundations.etale_simplicial_chains_basic_properties_hold
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := etale_cochain_complex_basic_properties_of_components
end LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
end
end

-- Source module: Development.EtaleCohomology.TateTwists.EtaleEvaluationMapConstructionOfComponents

section

@[expose] public section

namespace LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
theorem etale_evaluation_map_construction_of_components : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  apply LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := etale_evaluation_map_construction_of_components
end LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
end
end

-- Source module: Development.EtaleCohomology.TateTwists.EtaleFreeModuleCohomologyHomOfComponents

section

@[expose] public section

namespace LateralTheory.Fin.EtaleFreeSheafUniversalProperty
theorem etale_free_module_cohomology_hom_of_components : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := etale_free_module_cohomology_hom_of_components
end LateralTheory.Fin.EtaleFreeSheafUniversalProperty
end
end

-- Source module: Development.EtaleCohomology.TateTwists.CcAwFlipPf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.cupflip_ev_ext_pf : LateralTheory.EtaleFoundations.cupflip_ev_ext := by
  intro R _ E I n α β hab
  refine Cochain.ext _ _ fun p q hpq => ?_
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    have key : (chainsXIso R E N).inv ≫ α.v _ q hpq = (chainsXIso R E N).inv ≫ β.v _ q hpq := by
      refine (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R _ _).2.1 _ _ fun U x => ?_
      exact hab N q hpq U x
    simpa using congrArg (fun f => (chainsXIso R E N).hom ≫ f) key
  · have := (LateralTheory.Fin.EtaleSimplicialChainsFreeDescription.intersectionNumber_baseChange R).1 E
    have hz : IsZero (((chains R).obj E).X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    exact hz.eq_of_src _ _

namespace LateralTheory.EtaleFoundations

theorem ev_res' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  have h3 := (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R (E.obj (op (SimplexCategory.mk p))) (I.X s)).2.2.1 V U g x
  unfold ev
  rw [show Sx.res g x = (E.obj (op (SimplexCategory.mk p))).map g.op x from rfl, ← h3]
  have := congrArg (fun f => (ModuleCat.Hom.hom f) (freeGen R (E.obj (op (SimplexCategory.mk p))) U x))
    (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)
  simpa using this.symm

theorem along_res' {E : Spc} {p N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.along θ).res g = (x.res g).along θ := by
  unfold Sx.along Sx.res
  exact (NatTrans.naturality_apply (E.map θ.op) g.op x).symm

theorem cupflip_eta_mk_pf : cupflip_eta_mk := by
  intro h _ R _ I J K μ E n m k hk α β
  obtain ⟨η, hη⟩ := LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation.intersectionNumber_baseChange R (E := E) (I := K) (n := k - 1)
    (fun N s _ U x => phi μ hk α β x s (h N)) (by
      intro N s hs V U g x

      simp only [phi, Finsupp.sum, Sec.res, map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      unfold phiT
      split_ifs with hw
      · rw [map_zsmul]
        have := μ.nat g _ _ _ (by omega : -(z.1 : ℤ) + n + (-(z.2.1 : ℤ) + m) = s)
          (ev α z.1 _ rfl U (x.along z.2.2.1)) (ev β z.2.1 _ rfl U (x.along z.2.2.2))
        simp only [Sec.res] at this
        have ea := ev_res' α _ _ rfl g (x.along z.2.2.1)
        have eb := ev_res' β _ _ rfl g (x.along z.2.2.2)
        rw [along_res'] at ea eb
        simp only [Sec.res] at ea eb
        rw [this, ea, eb]
      · simp)
  exact ⟨η, fun N s hs U x => hη N s hs U x⟩

end LateralTheory.EtaleFoundations

theorem LateralTheory.EtaleFoundations.cc_aw_flip_of (hst : LateralTheory.EtaleFoundations.cupflip_steen) (hdl : LateralTheory.EtaleFoundations.cupflip_eta_delta) :
    LateralTheory.EtaleFoundations.cc_aw_flip :=
  LateralTheory.EtaleFoundations.cupflip_aw_flip_of hst (LateralTheory.EtaleFoundations.cupflip_homotopy_of LateralTheory.EtaleFoundations.cupflip_ev_ext_pf
    LateralTheory.EtaleFoundations.cupflip_eta_mk_pf hdl)
end
end
