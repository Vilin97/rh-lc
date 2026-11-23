module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GramIff
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsSemisimpleRepOfDetLawOfIsAlgClosed
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PhiMaps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IrrOfConn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrOpen

section

@[expose] public section

open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.Det.irrOpen :
    ∀ {A G ι : Type} [CommRing A] [Group G] [Fintype ι] [DecidableEq ι] (t : G → A),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (K : Type) [Field K] (φ : A →+* K) (ρ : G →* Matrix ι ι K) (p : PrimeSpectrum A), p.asIdeal = RingHom.ker φ →
        (∀ g, (ρ g).trace = φ (t g)) → (p ∈ U ↔ Submodule.span K (Set.range ρ) = ⊤) := by
  intro A G ι _ _ _ _ t
  refine ⟨⋃ g : ι × ι → G,
      ((PrimeSpectrum.basicOpen (Matrix.of fun a b => t (g a * g b)).det : TopologicalSpace.Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)),
    isOpen_iUnion (fun g => (PrimeSpectrum.basicOpen _).isOpen), ?_⟩
  intro K _ φ ρ p hp htr
  rw [UpperTheory.V.AlgebraTools.Det.gramIff, Set.mem_iUnion]
  apply exists_congr
  intro g
  have hM : φ.mapMatrix (Matrix.of fun a b => t (g a * g b)) =
      Matrix.of fun a b => (ρ (g a * g b)).trace := by
    ext a b
    show φ (t (g a * g b)) = (ρ (g a * g b)).trace
    rw [htr]
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, hp, RingHom.mem_ker, RingHom.map_det, hM]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MatIrrIff

section

@[expose] public section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.matIrrIff :
    ∀ {K G : Type} [Field K] [IsAlgClosed K] [Group G] {n : ℕ} (H : Subgroup G) (ρ : G →* Matrix (Fin n) (Fin n) K),
    U3.MatIrr H ρ ↔ Submodule.span K (Set.range fun h : H => ρ h) = ⊤ := by
  intro K G _ _ _ n H ρ
  have h := UpperTheory.V.AlgebraTools.Det.irrIffSpan (K := K) (ρ.comp H.subtype)
  refine Iff.trans ?_ h
  constructor
  · intro h1 N hN; exact h1 N fun g hg v hv => hN ⟨g, hg⟩ v hv
  · intro h1 N hN; exact h1 N fun g v hv => hN g g.2 v hv
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.StableField

section

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.stable_field :
    ∀ {n : ℕ} {A G κ κ' : Type} [CommRing A] [Group G] [Field κ] [IsAlgClosed κ] [Field κ'] [IsAlgClosed κ'] (D : GDet n A G) (f : A →+* κ) (f' : A →+* κ'), RingHom.ker f = RingHom.ker f' → (∃ ρ : G →* Matrix (Fin n) (Fin n) κ, UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f = GDet.ofRep ρ) → ∃ ρ : G →* Matrix (Fin n) (Fin n) κ', UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f' = GDet.ofRep ρ := by
  intro n A G κ κ' _ _ _ _ _ _ D f f' hker ⟨ρ, hρ, hD⟩
  obtain ⟨ρ', hD'⟩ : ∃ ρ' : G →* Matrix (Fin n) (Fin n) κ', D.map f' = GDet.ofRep ρ' := by
    obtain ⟨r, -, hr⟩ := exists_semisimple_rep_of_detLaw_of_isAlgClosed (D.map f').toDet
    let ρ' := r.toMonoidHom.comp (MonoidAlgebra.of κ' G)
    have hrep : GDet.repAlg ρ' κ' = r := by
      apply MonoidAlgebra.algHom_ext
      · intro g
        simp [GDet.repAlg, ρ', MonoidAlgebra.lift_single]
      · ext
    refine ⟨ρ', Eq.symm ?_⟩
    suffices h : (GDet.ofRep ρ').toDet = (D.map f').toDet by
      rw [← GDet.ofDet_toDet (GDet.ofRep ρ'), h, GDet.ofDet_toDet]
    rw [← hr, ← hrep]
    refine Det.ext' fun S _ _ x => ?_
    change (GDet.repAlg ρ' S (ofT κ' G S x)).det = (Det.repS (GDet.repAlg ρ' κ') S x).det
    congr 1
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      rw [ofT_tmul, Det.repS_tmul, map_smul]
      congr 1
      induction y using MonoidAlgebra.induction_linear with
      | zero => ext i j; simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]; ext i j; simp
      | single g a => ext i j; simp [GDet.repAlg]
  refine ⟨ρ', ?_, hD'⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    exact (UpperTheory.V.AlgebraTools.Det.matIrrIff ⊤ ρ').2 (Subsingleton.elim _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have htrace (K : Type) [Field K] (φ : A →+* K) (τ : G →* Matrix (Fin n) (Fin n) K)
      (hτ : D.map φ = GDet.ofRep τ) (g : G) :
      (τ g).trace = φ (D.tr (MonoidAlgebra.single g 1)) := by
    have hmap : (D.map φ).chi (MonoidAlgebra.single g 1) =
        (D.chi (MonoidAlgebra.single g 1)).map φ := by
      let _ : Algebra A K[X] := ((algebraMap K K[X]).comp φ).toAlgebra
      let ψ : A[X] →ₐ[A] K[X] :=
        { Polynomial.mapRingHom φ with commutes' := fun _ => Polynomial.map_C φ }
      have hψ (x : A[X]) : ψ x = x.map φ := rfl
      have h := D.nat A[X] K[X] ψ (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)
      simpa only [GDet.chi, GDet.map, map_sub, MonoidAlgebra.mapRingHom_single,
        AlgHom.coe_toRingHom, hψ, Polynomial.map_X, map_one] using h
    have hchi : (GDet.ofRep τ).chi (MonoidAlgebra.single g 1) = (τ g).charpoly := by
      simp only [GDet.chi, MonoidAlgebra.mapRingHom_single, map_one]
      change (GDet.repAlg τ K[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)).det = _
      rw [map_sub, Matrix.charpoly]
      congr 1
      ext i j
      by_cases hij : i = j <;> simp [GDet.repAlg, hij]
    rw [hτ, hchi] at hmap
    rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, hmap]
    simp [GDet.tr, GDet.lam]
  let H : Subgroup G := ⊤
  obtain ⟨U, -, hU⟩ := UpperTheory.V.AlgebraTools.Det.irrOpen (ι := Fin n)
    (fun g : H => D.tr (MonoidAlgebra.single (g : G) 1))
  let p : PrimeSpectrum A := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  have hp : p ∈ U := (hU κ f (ρ.comp H.subtype) p rfl (fun g => htrace κ f ρ hD g)).2
    ((UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ).1 hρ)
  exact (UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ').2
    ((hU κ' f' (ρ'.comp H.subtype) p hker (fun g => htrace κ' f' ρ' hD' g)).1 hp)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.StableOf

section

@[expose] public section

open IsLocalRing UpperTheory.V.Fr

private theorem exists_field_embedding_of_domain (D : Type) [CommRing D] [IsDomain D] :
    ∃ (K : Type) (_ : Field K) (j : D →+* K), Function.Injective j := by

  exact ⟨FractionRing D, inferInstance, algebraMap D _, IsFractionRing.injective D (FractionRing D)⟩

private theorem exists_algClosed_embedding_of_field (F : Type) [Field F] :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (j : F →+* K), Function.Injective j :=
  ⟨AlgebraicClosure F, inferInstance, inferInstance, algebraMap F _, RingHom.injective _⟩

private theorem exAlgCl0 (R : Type) [CommRing R] (P : Ideal R) [P.IsPrime] :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (j : R →+* K), RingHom.ker j = P := by
  haveI : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
  obtain ⟨K0, hK0, j0, hj0⟩ := exists_field_embedding_of_domain (R ⧸ P)
  obtain ⟨K, hK, hc, j, hj⟩ := exists_algClosed_embedding_of_field K0
  refine ⟨K, hK, hc, (j.comp j0).comp (Ideal.Quotient.mk P), ?_⟩
  have hinj : Function.Injective (j.comp j0) := fun a b h => hj0 (hj h)
  rw [RingHom.ker_comp_of_injective _ hinj, Ideal.mk_ker]

private theorem exAlgCl (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (P : Ideal R) [P.IsPrime] :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra O K) (j : R →ₐ[O] K), RingHom.ker (j : R →+* K) = P := by
  obtain ⟨K, hK, hc, j, hj⟩ := exAlgCl0 R P
  letI : Algebra O K := (j.comp (algebraMap O R)).toAlgebra
  exact ⟨K, hK, hc, inferInstance, ⟨j, fun _ => rfl⟩, hj⟩

private theorem ringHom_injective_of_fields {F K : Type} [Field F] [Field K] (g : F →+* K) :
    Function.Injective g :=
  RingHom.injective _


theorem UpperTheory.V.Pr.stableOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.StableOf := by
  intro l _ O _ _ _ _ _ F n T
  unfold UpperTheory.V.Pr.Setup.StableOf
  intro Φ hΦ x L P _ hTI
  have hn := T.n23
  have hok := T.ok
  obtain ⟨K, hK, hc, _, j, hj⟩ := exAlgCl O L.R P
  let f : T.S.A →ₐ[O] K := j.comp L.ι
  have hkerf : RingHom.ker (f : T.S.A →+* K) = L.im P := by
    show RingHom.ker ((j : L.R →+* K).comp (L.ι : T.S.A →+* L.R)) =
      Ideal.comap (L.ι : T.S.A →+* L.R) P
    rw [← RingHom.comap_ker, hj]
  have hloc := (loc_rho hok hn T.S x L).2.2.1 P
  have hTIS : T.S.u.TI (RingHom.ker (f : T.S.A →+* K)) := by
    rw [hkerf]
    unfold NRep.TI NRep.OffTri at hTI ⊢
    exact ⟨⟨fun h => hTI.1.1 (hloc.1.mpr h), fun h => hTI.1.2 (hloc.2.1.mpr h)⟩,
      fun h3 h => hTI.2 h3 (hloc.2.2.mpr h)⟩
  have hirr := ((types hok hn T.S K (f : T.S.A →+* K)).1).mpr hTIS
  have hirr2 := T.K.tw_irr (NRep.map (f : T.S.A →+* K) T.S.u) hirr
  have hΦ' : T.K.IsPhi T.B T.S Φ := hΦ
  have hm := UpperTheory.V.Pr.TwLink.IsPhi.maps T.K hΦ' f
  unfold UpperTheory.V.W.Pair.Maps at hm
  have hL : RingHom.ker ((f.comp (T.S.inc.comp Φ)) : T.B.B →+* K) =
      Ideal.comap ((T.phi Φ L) : T.B.B →+* L.R) P := by
    show RingHom.ker ((j : L.R →+* K).comp ((T.phi Φ L) : T.B.B →+* L.R)) = _
    rw [← RingHom.comap_ker, hj]
  have hR : RingHom.ker (T.B.toKap (T.back Φ L P)) = (T.back Φ L P).asIdeal := by
    unfold UpperTheory.V.W.UniversalOrdinaryDeterminantRing.toKap
    refine (RingHom.ker_comp_of_injective _ (ringHom_injective_of_fields _)).trans ?_
    exact Ideal.ker_algebraMap_residueField _
  unfold UpperTheory.V.W.UniversalOrdinaryDeterminantRing.IsStable
  refine UpperTheory.V.CA.stable_field T.B.u.D ((f.comp (T.S.inc.comp Φ)) : T.B.B →+* K)
    (T.B.toKap (T.back Φ L P)) ?_ ⟨_, hirr2, hm.1⟩
  rw [hL, hR]
  rfl
end
end
