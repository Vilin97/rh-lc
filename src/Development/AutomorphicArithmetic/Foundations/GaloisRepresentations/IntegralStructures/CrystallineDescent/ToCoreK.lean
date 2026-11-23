module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.TLiftK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.LimOddOfLimFinOdd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ChrExPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ChrPairsPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ConjDivNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ExpInj
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadExp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.TypProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.TypVal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LiftSatUHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.MapUnivAdd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PBaseNG
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatId
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadEx

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr


theorem UpperTheory.Gal.TP.Chr.readEx :
    UpperTheory.Gal.TP.Chr.ReadEx := by
  intro E _ _ _ μ hU
  let e := GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)
  let f : (AE (↥(maximalRealSubfield E)) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ := Units.map (e : _ →* _)
  refine ⟨{ toFun := fun z => ⟨((μ.1 (f z) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hU (f z))⟩,
            map_one' := ?_, map_mul' := ?_ }, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp
  · intro x y
    apply Subtype.ext
    simp only [map_mul, Units.val_mul]
    rfl
  · intro z
    rfl
  · have hf : Continuous f := by
      show Continuous (Units.map (e : AE (↥(maximalRealSubfield E)) E →* AdeleRing (𝓞 E) E))
      exact Continuous.units_map _ (GlobalTheory.UnitaryHeckeBaseChange.continuous_toAdele _ E)
    have hμc : Continuous (μ.1 : Ideles E → ℂˣ) := μ.2.1
    refine continuous_induced_rng.2 ?_
    exact Units.continuous_val.comp (hμc.comp hf)
  · intro x
    apply Subtype.ext
    show ((μ.1 (f _) : ℂˣ) : ℂ) = 1
    rw [show f _ = diagUnits E x from Units.ext ?_, μ.2.2 x]
    · rfl
    · exact GlobalTheory.UnitaryHeckeBaseChange.toAdele_incA (x : E)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadRes

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr
open scoped TensorProduct

theorem UpperTheory.Gal.TP.Chr.readRes :
    UpperTheory.Gal.TP.Chr.ReadRes := by
  intro E _ _ _ μ χ hR hμ a
  rw [hR]
  have h3 : ∀ {σ : E →ₐ[↥(maximalRealSubfield E)] E} (h : HeckeCharacterZeroLocus.ThmBIn.IsCMExt (↥(maximalRealSubfield E)) E σ),
      Units.map ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv h).toRingHom
        : AE (↥(maximalRealSubfield E)) E →* AdeleRing (𝓞 E) E)
      (Units.map (algebraMap (AF ↥(maximalRealSubfield E)) (AE (↥(maximalRealSubfield E)) E)
        : AF ↥(maximalRealSubfield E) →* AE (↥(maximalRealSubfield E)) E) a)
      = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E a := fun _ =>
    Units.ext (GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap (a : AF ↥(maximalRealSubfield E)))
  erw [h3 (GlobalTheory.GalOfCusp.isCMExt_real E), hμ a]
  simp only [GlobalTheory.GalOfCusp.quadChar, MonoidHom.comp_apply]
  split_ifs with hm
  · obtain ⟨y, ⟨t, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 hm
    have hn : GlobalTheory.IdeleNormChar.normSign E a = 1 := by
      refine (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).2 ⟨t, ?_⟩
      rw [← hyz]
      simpa [GlobalTheory.QuadSymbol.toUnits, GlobalTheory.QuadSymbol.normGroup] using hz
    simp [hn]
  · rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with hn | hn
    · exfalso
      obtain ⟨t, ht⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 hn
      exact hm (Subgroup.mem_sup.2 ⟨_, ⟨t, rfl⟩, _, ht, mul_div_cancel _ _⟩)
    · simp [hn]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ChrPairsHolds

section

@[expose] public section

namespace UpperTheory.Gal.TP.Chr

theorem chrEx_holds : ChrEx := chrEx muEmb readEx readLoc readRes readExp absFacts (typProd typVal) expInj

theorem chrPairs_holds : UpperTheory.Gal.TP.Sub.ChrPairs := chrPairs chrEx_holds typVal

end UpperTheory.Gal.TP.Chr
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PEmbSplit

section

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.embSplit_holds :
    EmbSplit := by
  intro E _ _ _ emb
  have hcj : ∀ (φ : E →+* ℂ), (ComplexEmbedding.conjugate φ).comp
      (algebraMap (maximalRealSubfield E) E) =
      ComplexEmbedding.conjugate (φ.comp (algebraMap (maximalRealSubfield E) E)) := by
    intro φ
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hinj : ∀ (w w' : InfinitePlace (maximalRealSubfield E)), w.embedding = w'.embedding → w = w' := by
    intro w w' h
    rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h]
  refine ⟨?_, ?_, ?_⟩
  · intro τ
    let w := InfinitePlace.mk (τ.comp (algebraMap (maximalRealSubfield E) E))
    refine ⟨w, ?_⟩
    have hw : (InfinitePlace.mk τ).comap (algebraMap (maximalRealSubfield E) E) =
        (InfinitePlace.mk (emb w).1).comap (algebraMap (maximalRealSubfield E) E) := by
      rw [InfinitePlace.comap_mk, InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
    have hmk : InfinitePlace.mk τ = InfinitePlace.mk (emb w).1 :=
      (IsCMField.equivInfinitePlace E).injective hw
    rcases InfinitePlace.mk_eq_iff.1 hmk with h | h
    · exact Or.inl h
    · right
      rw [← h]
      ext x
      simp [ComplexEmbedding.conjugate_coe_eq]
  · intro w w' h
    apply hinj
    rw [← (emb w).2, ← (emb w').2, h]
  · intro w w' h
    have h1 : w.embedding = ComplexEmbedding.conjugate w'.embedding := by
      rw [← (emb w).2, ← (emb w').2, h, hcj]
    have hww : w = w' := by
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h1,
        InfinitePlace.mk_conjugate_eq]
    subst hww
    apply IsTotallyComplex.complexEmbedding_not_isReal (emb w).1
    exact h.symm
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.UpOfHolds

section

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.upOf_holds :
    EmbSplit → WtId → SatId → UpperTheory.Gal.TP.Loc.LiftSatU → UpOf := by
  intro hE hWt hS hLS E _ _ _ n t hn hnt Bs χX χW mX mW U hU lam hl U' hL κ m ψ p hD
  classical
  obtain ⟨hcov, -, hne⟩ := hE E Bs.emb
  choose l' hl'w hl'L using hL.wt
  choose w₀ hw₀ using hcov
  have hn' : 1 ≤ n + t := by omega
  let lam' : (E →+* ℂ) → DomWeight (n + t) := fun τ =>
    if τ = (Bs.emb (w₀ τ)).1 then l' (w₀ τ) else (l' (w₀ τ)).dual
  have key : ∀ τ, (∃ w, τ = (Bs.emb w).1 ∧ lam' τ = l' w) ∨
      ∃ w, τ = ComplexEmbedding.conjugate (Bs.emb w).1 ∧ lam' τ = (l' w).dual := by
    intro τ
    rcases hw₀ τ with h | h
    · exact Or.inl ⟨w₀ τ, h, if_pos h⟩
    · exact Or.inr ⟨w₀ τ, h, if_neg fun h' => hne (w₀ τ) (w₀ τ) (h'.symm.trans h)⟩
  refine ⟨lam', hL.aut, fun τ => ?_, hD.alg, fun τ => ?_, ?_⟩
  · rcases key τ with ⟨w, rfl, h⟩ | ⟨w, rfl, h⟩
    · rw [h]
      exact hl'w w
    · rw [h]
      exact GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn' (hl'w w)
  · rcases key τ with ⟨w, rfl, h⟩ | ⟨w, rfl, h⟩
    · rw [h]
      exact (hWt n t _ _ _ _ (hl'L w)).1 _ (fun i => p i _) (hD.m₁ w) fun i => hD.p₁ i w
    · have hd : lam (ComplexEmbedding.conjugate (Bs.emb w).1) = (lam (Bs.emb w).1).dual :=
        GlobalTheory.DefU.hasWeightAt_unique ⟨U, hU⟩ _ (hl _) (GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn (hl _))
      rw [h, hd]
      exact (hWt n t _ _ _ _ (hl'L w)).2 _ (fun i => p i _) (hD.m₂ w) fun i => hD.p₂ i w
  · intro v hv hκ hψ B hB
    obtain ⟨hX, hW, hk, hc⟩ := hD.loc v hκ hψ
    have h1 := hLS E n (n + t) (by omega) Bs χX χW mX mW _ U U' hU hL v hv hX hW B hB
    rw [Nat.add_sub_cancel_left] at h1
    refine ⟨_, h1, ?_⟩
    have hnorm : normV v = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
    rw [hnorm]
    exact hS E v n t B _ _ _ (fun i => (((ψ i).val v : ℂˣ) : ℂ)) hk hc
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.UpMain

section

@[expose] public section

namespace UpperTheory.Gal.TP.Sub

theorem upOf : UpOf := upOf_holds embSplit_holds wtId_holds satId_holds UpperTheory.Gal.TP.Loc.liftSatU_holds

theorem baseNG : BaseNG := baseNG_holds UpperTheory.Gal.TP.Skew.skewLine_holds

end UpperTheory.Gal.TP.Sub
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.TwoUpOKOfSteps

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP

open Sub

theorem twoUpOK_of_steps (hT : UpperTheory.TP.TLiftK) (hC : ChrPairs) (hU : UpOf) (hB : BaseNG) : TwoUpOK := by
  intro E _ _ _ hE hK _ hI n hn he U hA lam hl w₀ hw₀
  obtain ⟨Bs, δ, 𝔞, hG, hX, hW⟩ := hB E hE hI
  obtain ⟨d₀, hd⟩ := hT E Bs ⟨hG.cm, hK, hG.unram, hG.std, hG.inert, hG.psiP⟩ n hn _ rfl (hX n)
  set t := 2 * (d₀ + n) + 1 with ht
  obtain ⟨b, hb⟩ := (Set.finite_range fun x : InfinitePlace (maximalRealSubfield E) × Fin n => (lam (Bs.emb x.1).1).w x.2).bddBelow
  obtain ⟨κ, m, χX, χW, mX, mW, ψ, p, hκ, hj, hne, hu, hu'⟩ :=
    hC E hE n t he ⟨_, rfl⟩ Bs.emb (2 * b - ((n + t : ℕ) : ℤ)) w₀ hw₀
  have key : ∀ j, ∃ U' lam', IsUp U lam κ m U' lam' (ψ j) (p j) := fun j => by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hj j
    obtain ⟨U', hL⟩ := hd (n + t) (by omega) _ δ rfl (hW (n + t)) (χX j) (χW j) (mX j) (mW j) a1 a2 a3 a4 a5 a6 U
      (fun w => lam (Bs.emb w).1) hA (fun w => hl _) fun w k => by
        have h1 := a7 w
        have h2 : b ≤ (lam (Bs.emb w).1).w k := hb ⟨(w, k), rfl⟩
        omega
    exact ⟨U', hU E n t hn (by omega) Bs _ _ _ _ U hA lam hl U' hL κ m _ _ a8⟩
  obtain ⟨U₁, l₁, h₁⟩ := key 0
  obtain ⟨U₂, l₂, h₂⟩ := key 1
  exact ⟨t, κ, m, U₁, U₂, l₁, l₂, ψ 0, ψ 1, p 0, p 1, he.add_odd ⟨_, rfl⟩, hκ, h₁, h₂, hne, hu, hu'⟩

theorem twoUpOK_of_k (h : UpperTheory.TP.TLiftK) : TwoUpOK := twoUpOK_of_steps h Chr.chrPairs_holds upOf baseNG

end UpperTheory.Gal.TP
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.ToCoreK

section

@[expose] public section

namespace UpperTheory.Gal.Int.Core

theorem toCoreK (hT : UpperTheory.TP.TLiftK) :
    GlobalTheory.CongPhi.ClosedPhi → GlobalTheory.Cong.DescOffT → GlobalTheory.CongL.LimFinOdd → GlobalTheory.RoadU.Core :=
  toCore (UpperTheory.Gal.TP.twoUpOK_of_k hT)

end UpperTheory.Gal.Int.Core
end
end
