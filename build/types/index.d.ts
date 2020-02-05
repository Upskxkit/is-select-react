import React, { ReactElement } from "react";
import PropTypes from "prop-types";
import "./index.scss";
import { SelectWrapper } from "./interface";
declare function Select({ type, multi, placeholder, onSelect, className, list, value, defaultValue, request, hasError }: SelectWrapper): ReactElement;
declare namespace Select {
    var propTypes: {
        multi: PropTypes.Requireable<boolean>;
        hasError: PropTypes.Requireable<boolean>;
        type: PropTypes.Requireable<string>;
        placeholder: PropTypes.Requireable<string>;
        iconUrl: PropTypes.Requireable<string>;
        className: PropTypes.Requireable<string>;
        onSelect: PropTypes.Requireable<(...args: any[]) => any>;
        list: PropTypes.Requireable<any[]>;
        value: PropTypes.Requireable<any>;
        request: PropTypes.Requireable<(...args: any[]) => any>;
    };
}
declare const _default: React.MemoExoticComponent<typeof Select>;
export default _default;
