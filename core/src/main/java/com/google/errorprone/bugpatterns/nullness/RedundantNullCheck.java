/*
 * Copyright 2025 The Error Prone Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.google.errorprone.bugpatterns.nullness;

import static com.google.errorprone.BugPattern.SeverityLevel.WARNING;
import static com.google.errorprone.matchers.Description.NO_MATCH;
import static com.google.errorprone.matchers.method.MethodMatchers.staticMethod;

import com.google.errorprone.BugPattern;
import com.google.errorprone.VisitorState;
import com.google.errorprone.bugpatterns.BugChecker;
import com.google.errorprone.bugpatterns.BugChecker.BinaryTreeMatcher;
import com.google.errorprone.bugpatterns.BugChecker.MemberReferenceTreeMatcher;
import com.google.errorprone.bugpatterns.BugChecker.MethodInvocationTreeMatcher;
import com.google.errorprone.dataflow.nullnesspropagation.Nullness;
import com.google.errorprone.dataflow.nullnesspropagation.NullnessAnnotations;
import com.google.errorprone.matchers.Description;
import com.google.errorprone.matchers.Matcher;
import com.google.errorprone.util.ASTHelpers;
import com.google.errorprone.util.TargetType;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ClassTree;
import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.MemberReferenceTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Types;
import java.util.Optional;
import javax.lang.model.element.ElementKind;

@BugPattern(
    summary =
        "Explicit null check on a variable or method call that is not @Nullable within a"
            + " @NullMarked scope.",
    severity = WARNING)
public class RedundantNullCheck extends BugChecker
    implements BinaryTreeMatcher, MethodInvocationTreeMatcher, MemberReferenceTreeMatcher {

  private static final Matcher<ExpressionTree> OBJECTS_NON_NULL_METHOD =
      staticMethod()
          .onClass("java.util.Objects")
          .named("nonNull")
          .withParameters("java.lang.Object");

  private static final Matcher<MethodInvocationTree> OBJECTS_NON_NULL_INVOCATION =
      com.google.errorprone.matchers.Matchers.anyOf(OBJECTS_NON_NULL_METHOD);

  @Override
  public Description matchBinary(BinaryTree tree, VisitorState state) {
    if (NullnessUtils.getNullCheck(tree) == null) {
      return NO_MATCH;
    }

    ExpressionTree expression =
        tree.getLeftOperand().getKind() == Tree.Kind.NULL_LITERAL
            ? tree.getRightOperand()
            : tree.getLeftOperand();

    if (isCheckRedundant(expression, state)) {
      return buildDescription(tree).build();
    }
    return NO_MATCH;
  }

  @Override
  public Description matchMethodInvocation(MethodInvocationTree tree, VisitorState state) {
    if (OBJECTS_NON_NULL_INVOCATION.matches(tree, state)) {
      if (isCheckRedundant(tree.getArguments().get(0), state)) {
        return buildDescription(tree).build();
      }
    }
    return NO_MATCH;
  }

  private static boolean isCheckRedundant(ExpressionTree expression, VisitorState state) {
    Symbol symbol = ASTHelpers.getSymbol(expression);
    if (symbol instanceof VarSymbol) {
      return isVarSymbolCheckRedundant((VarSymbol) symbol, state);
    }
    if (symbol instanceof MethodSymbol) {
      return !isEffectivelyNullable((MethodSymbol) symbol, state);
    }
    return false;
  }

  private static boolean isVarSymbolCheckRedundant(VarSymbol varSymbol, VisitorState state) {
    if (!NullnessUtils.isInNullMarkedScope(varSymbol, state)) {
      return false;
    }
    if (NullnessUtils.isAlreadyAnnotatedNullable(varSymbol)) {
      return false;
    }

    VariableTree varDecl = NullnessUtils.findDeclaration(state, varSymbol);

    if ((varSymbol.getKind() == ElementKind.LOCAL_VARIABLE
            || varSymbol.getKind() == ElementKind.RESOURCE_VARIABLE)
        && varDecl != null) {

      if (varDecl.getInitializer() == null) {
        return false;
      }

      Tree initializer = varDecl.getInitializer();

      if (initializer.getKind() == Tree.Kind.METHOD_INVOCATION) {
        MethodInvocationTree methodInvocation = (MethodInvocationTree) initializer;
        MethodSymbol methodSymbol = ASTHelpers.getSymbol(methodInvocation);
        if (methodSymbol != null && isEffectivelyNullable(methodSymbol, state)) {
          return false;
        }
      } else {
        return false;
      }
    }
    return true;
  }

  @Override
  public Description matchMemberReference(MemberReferenceTree tree, VisitorState state) {
    if (!OBJECTS_NON_NULL_METHOD.matches(tree, state)) {
      return NO_MATCH;
    }

    TargetType targetType = TargetType.targetType(state);
    if (targetType == null) {
      return NO_MATCH;
    }
    Type functionalInterfaceType = targetType.type();

    Types types = state.getTypes();
    Symbol samSymbol = types.findDescriptorSymbol(functionalInterfaceType.tsym);
    if (!(samSymbol instanceof MethodSymbol)) {
      return NO_MATCH;
    }
    MethodSymbol sam = (MethodSymbol) samSymbol;
    if (sam.getParameters().size() != 1) {
      return NO_MATCH;
    }

    VarSymbol paramSymbol = sam.getParameters().get(0);
    Type paramType = types.memberType(functionalInterfaceType, paramSymbol);
    if (NullnessAnnotations.fromAnnotationsOn(paramType).orElse(Nullness.NONNULL) == Nullness.NULLABLE) {
      return NO_MATCH;
    }

    Symbol enclosing = null;
    MethodTree enclosingMethod = ASTHelpers.findEnclosingNode(state.getPath(), MethodTree.class);
    if (enclosingMethod != null) {
      enclosing = ASTHelpers.getSymbol(enclosingMethod);
    } else {
      ClassTree enclosingClass = ASTHelpers.findEnclosingNode(state.getPath(), ClassTree.class);
      if (enclosingClass != null) {
        enclosing = ASTHelpers.getSymbol(enclosingClass);
      }
    }

    if (enclosing != null && NullnessUtils.isInNullMarkedScope(enclosing, state)) {
      return buildDescription(tree).build();
    }
    return NO_MATCH;
  }

  private static boolean isEffectivelyNullable(MethodSymbol methodSymbol, VisitorState state) {
    Optional<Nullness> returnTypeNullness = NullnessAnnotations.fromAnnotationsOn(methodSymbol);
    if (returnTypeNullness.isPresent()) {
      // Explicit @Nullable or @NonNull on the return type
      return returnTypeNullness.get() == Nullness.NULLABLE;
    }
    // No explicit annotation on return type.
    // Default based on the null-marked status of the method's defining scope.
    // If the method's defining scope is NOT @NullMarked (or is @NullUnmarked),
    // its unannotated return type is effectively nullable.
    return !NullnessUtils.isInNullMarkedScope(methodSymbol, state);
  }
}
