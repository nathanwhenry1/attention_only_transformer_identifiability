import AnyLayerIdentifiabilityProof.NLayer.Genericity.GenericityMain
import AnyLayerIdentifiabilityProof.NLayer.Foundations.ParamPolynomialGenericity
import AnyLayerIdentifiabilityProof.NLayer.Foundations.PolynomialGenericity

set_option autoImplicit false

open MeasureTheory Matrix MvPolynomial

namespace TransformerIdentifiability.NLayer

/-!
# Nullness of the exact TeX generic bad set

This shard isolates the measure-theoretic part of the exact TeX genericity null-set
argument.  Once the algebraic shard supplies a finite family of nonzero coordinate
polynomials whose common nonvanishing locus implies `TexGeneric`, nullness follows
immediately from `paramNonvanishingCarrier_compl_null`.

The algebraic witness is supplied by the later polynomial-cover shard.  Its hard
content is the coefficient polynomial construction for the recursive TeX clauses,
especially `(G4)` as currently represented by `TexAnchorCertificate`.
-/

/-- A finite coordinate-polynomial nonvanishing package strong enough to imply the
exact TeX genericity predicate. -/
structure TexGenericPolynomialNonvanishingCover (L d : Nat) : Type 1 where
  κ : Type
  data : PolynomialNonvanishingData (ParamCoord L d) κ
  carrier_subset_texGeneric : paramNonvanishingCarrier data ⊆ TexGenericSet L d

namespace TexGenericPolynomialNonvanishingCover

/-- The exceptional set attached to a TeX-generic polynomial cover. -/
def badSet {L d : Nat} (C : TexGenericPolynomialNonvanishingCover L d) :
    Set (Params L d) :=
  (paramNonvanishingCarrier C.data)ᶜ

/-- The cover's exceptional set is null by the parameter-polynomial genericity bridge. -/
theorem badSet_null {L d : Nat} (C : TexGenericPolynomialNonvanishingCover L d) :
    volume (C.badSet : Set (Params L d)) = 0 := by
  simpa [badSet] using paramNonvanishingCarrier_compl_null C.data

/-- The exact TeX bad set is contained in the polynomial exceptional set of any cover. -/
theorem texGenericBadSet_subset_badSet {L d : Nat}
    (C : TexGenericPolynomialNonvanishingCover L d) :
    TexGenericBadSet L d ⊆ C.badSet := by
  intro θ hθ hθpoly
  exact hθ (C.carrier_subset_texGeneric hθpoly)

end TexGenericPolynomialNonvanishingCover

/-- If a finite coordinate-polynomial nonvanishing package implies `TexGeneric`, then
the exact TeX bad set is Lebesgue-null. -/
theorem texGenericBadSet_null_of_paramNonvanishingCarrier_subset
    {L d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (ParamCoord L d) κ)
    (hsubset : paramNonvanishingCarrier D ⊆ TexGenericSet L d) :
    volume (TexGenericBadSet L d : Set (Params L d)) = 0 := by
  refine measure_mono_null ?_ (paramNonvanishingCarrier_compl_null D)
  intro θ hθ hθpoly
  exact hθ (hsubset hθpoly)

/-- Equality with a finite coordinate-polynomial nonvanishing carrier is a special case
of the subset interface. -/
theorem texGenericBadSet_null_of_paramNonvanishingCarrier_eq
    {L d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (ParamCoord L d) κ)
    (hcarrier : paramNonvanishingCarrier D = TexGenericSet L d) :
    volume (TexGenericBadSet L d : Set (Params L d)) = 0 :=
  texGenericBadSet_null_of_paramNonvanishingCarrier_subset D (by
    intro θ hθ
    simpa [hcarrier] using hθ)

/-- Packaged version of `texGenericBadSet_null_of_paramNonvanishingCarrier_subset`. -/
theorem texGenericBadSet_null_of_polynomialNonvanishingCover
    {L d : Nat} (C : TexGenericPolynomialNonvanishingCover L d) :
    volume (TexGenericBadSet L d : Set (Params L d)) = 0 := by
  exact measure_mono_null
    (TexGenericPolynomialNonvanishingCover.texGenericBadSet_subset_badSet C)
    (TexGenericPolynomialNonvanishingCover.badSet_null C)

end TransformerIdentifiability.NLayer
