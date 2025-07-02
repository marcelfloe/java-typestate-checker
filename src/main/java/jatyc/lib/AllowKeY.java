package jatyc.lib;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.TYPE, ElementType.CONSTRUCTOR})

/**
 * Indicates that the typestate checker is allowed to refer to KeY when making typestate decisions.
 * This can be applied to methods and constructors, as well as classes/interfaces (indicating, that KeY can be used for every method/constructor).
 * Using KeY requires JML contracts and will result in a performance penalty.
 * It also allows the typestate checker to allow less defensive programming.
 * When using typestate transitions based on return values with classes or numeric values,
 * KeY is used automatically (annotation can be omitted, JML still required).
 */
public @interface AllowKeY {
}
