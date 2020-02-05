import React from "react";
import PropTypes from "prop-types";
import "./SelectButton.scss";
import { SelectButtonInput } from "../../interface";
declare const _default: React.MemoExoticComponent<{
    ({ handleClick, pending, className, value, placeholder, type, opened, hasError }: SelectButtonInput): React.ReactElement<any, string | ((props: any) => React.ReactElement<any, string | any | (new (props: any) => React.Component<any, any, any>)> | null) | (new (props: any) => React.Component<any, any, any>)>;
    propTypes: {
        handleClick: PropTypes.Requireable<(...args: any[]) => any>;
        pending: PropTypes.Requireable<boolean>;
        opened: PropTypes.Requireable<boolean>;
        className: PropTypes.Requireable<string>;
        value: PropTypes.Requireable<string>;
        placeholder: PropTypes.Requireable<string>;
        type: PropTypes.Requireable<string>;
    };
}>;
export default _default;
