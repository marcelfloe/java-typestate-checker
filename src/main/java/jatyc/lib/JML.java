package jatyc.lib;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * This annotation is used to hold JML contracts.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({
  ElementType.METHOD, ElementType.TYPE, ElementType.CONSTRUCTOR,
  ElementType.ANNOTATION_TYPE, ElementType.TYPE_USE, ElementType.FIELD,
  ElementType.LOCAL_VARIABLE, ElementType.MODULE, ElementType.PACKAGE,
  ElementType.PARAMETER, ElementType.RECORD_COMPONENT, ElementType.TYPE_PARAMETER
})
public @interface JML {
  String value();
}
