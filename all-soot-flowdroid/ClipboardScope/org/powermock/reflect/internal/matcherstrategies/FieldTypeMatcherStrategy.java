/*
 * Copyright 2008 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.powermock.reflect.internal.matcherstrategies;

import org.powermock.reflect.exceptions.FieldNotFoundException;

import java.lang.reflect.Field;

public class FieldTypeMatcherStrategy extends FieldMatcherStrategy {

    final Class<?> expectedFieldType;

    public FieldTypeMatcherStrategy(Class<?> fieldType) {
        if (fieldType == null) {
            throw new IllegalArgumentException("field type cannot be null.");
        }
        this.expectedFieldType = fieldType;
    }

    @Override
    public boolean matches(Field field) {
        return expectedFieldType.equals(field.getType());
    }

    @Override
    public void notFound(Class<?> type, boolean isInstanceField) throws FieldNotFoundException {
        throw new FieldNotFoundException(String.format("No %s field of type \"%s\" could be found in the class hierarchy of %s.",
                isInstanceField ? "instance" : "static", expectedFieldType.getName(), type.getName()));
    }

    @Override
    public String toString() {
        return "type " + expectedFieldType.getName();
    }
}